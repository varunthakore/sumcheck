use crate::poly::{MultiPoly, UniPoly};
use ff::Field;
use neptune::poseidon::PoseidonConstants;

use ff::PrimeField;
use neptune::Arity;

use neptune::sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    vanilla::{Mode, Sponge, SpongeTrait},
};

// Sumcheck proof stores vector of Univariate polynomials
#[derive(Clone, Debug)]
pub struct Sumcheck<F: Field> {
    pub polys: Vec<UniPoly<F>>,
}

impl<F: Field + PrimeField> Sumcheck<F> {
    // Sumcheck Prover
    #[allow(dead_code)]
    fn prove<A: Arity<F>>(
        claim: F,
        g: MultiPoly<F>,
        transcript: &mut Transcript<F>,
    ) -> Result<Sumcheck<F>, SumcheckError> {
        // Append claim to transcript
        transcript.state.push(claim);

        let mut r = vec![];

        let num_rounds = g.num_vars;

        let mut polys = vec![];

        for j in 0..num_rounds {
            // compute univariate polynomial from multivariate polynomial
            let poly = g.to_univariate(j, r.clone());

            // Append polynomial to transcript
            transcript.absorb(poly.clone());

            // Squeeze to get random field element
            let r_j = transcript.hash::<A>();
            r.push(r_j);

            // append univariate polynomial
            polys.push(poly);
        }

        Ok(Sumcheck { polys })
    }

    // Sumcheck Verifier
    #[allow(dead_code)]
    fn verify<A: Arity<F>>(
        &self,
        claim: F,
        degree_bound: usize,
        num_rounds: usize,
        g: MultiPoly<F>,
        transcript: &mut Transcript<F>,
    ) -> Result<bool, SumcheckError> {
        // Check number of polynomials in Sumcheck proof is valid
        if self.polys.len() != num_rounds {
            return Err(SumcheckError::InvalidUniPolys);
        }

        let mut claim_per_round = claim;

        // Append claim to transcript
        transcript.state.push(claim);

        let mut r = vec![];

        for (j, poly) in self.polys.iter().enumerate() {
            // Check degree bound of univariate polynomial
            if poly.degree() > degree_bound {
                return Err(SumcheckError::InvalidDegree);
            }

            // Check claim is valid
            let claim_calc = poly.evluate_at_zero() + poly.evaluate_at_one();
            if claim_calc != claim_per_round {
                return Err(SumcheckError::InvalidClaim);
            }

            // Append polynomial to transcript
            transcript.absorb(poly.clone());

            // Squeeze to get random field element
            let r_j = transcript.hash::<A>();
            r.push(r_j);

            // compute claim for next round
            claim_per_round = poly.evaluate(r[j]);
        }

        // Check final claim with single query to multivariate polynomial g
        let claim_exp = g.evaluate(r);
        Ok(claim_per_round == claim_exp)
    }
}

#[derive(Debug, thiserror::Error, PartialEq)]
pub enum SumcheckError {
    #[error("Invalid Number of Univariate Ploynomials in Sumcheck Proof")]
    InvalidUniPolys,

    #[error("Invalid Degree of Univariate Ploynomials in Sumcheck Proof")]
    InvalidDegree,

    #[error("Invalid Claim of Polynomial")]
    InvalidClaim,
}

pub struct Transcript<F: Field> {
    state: Vec<F>,
}

impl<F: Field + PrimeField> Default for Transcript<F> {
    fn default() -> Self {
        Transcript { state: vec![] }
    }
}

impl<F: Field + PrimeField> Transcript<F> {
    pub fn absorb(&mut self, poly: UniPoly<F>) {
        let mut vec = poly.coeffs;

        let mut new_state = self.state.clone();

        new_state.append(&mut vec);
    }

    pub fn hash<A: Arity<F>>(&self) -> F {
        let p: PoseidonConstants<F, A> = PoseidonConstants::new_constant_length(self.state.len());
        let parameter = IOPattern(vec![
            SpongeOp::Absorb(self.state.len() as u32),
            SpongeOp::Squeeze(1),
        ]);
        let mut sponge = Sponge::new_with_constants(&p, Mode::Simplex);
        let acc = &mut ();

        sponge.start(parameter, None, acc);
        SpongeAPI::absorb(&mut sponge, self.state.len() as u32, &self.state, acc);

        let output = SpongeAPI::squeeze(&mut sponge, 1, acc);
        assert_eq!(output.len(), 1);

        sponge.finish(acc).unwrap();

        output[0]
    }
}

#[cfg(test)]
mod test {

    use super::Sumcheck;
    use crate::{
        poly::{MultiPoly, Term, UniPoly},
        sumcheck::{SumcheckError, Transcript},
    };
    use ff::Field;
    use generic_array::typenum::U2;
    use pasta_curves::Fp;

    #[test]
    fn test_sumcheck() {
        {
            // g(X0, X1, X2) = 2 * (X0 ^ 3) + X0 * X2 + X1 * X2
            let term0 = Term(vec![(0, 3)]);
            let term1 = Term(vec![(0, 1), (2, 1)]);
            let term2 = Term(vec![(1, 1), (2, 1)]);
            let g = MultiPoly {
                num_vars: 3,
                terms: vec![(Fp::from(2u64), term0), (Fp::ONE, term1), (Fp::ONE, term2)],
            };
            let claim = Fp::from(12u64);
            let num_rounds = 3;
            let degree_bound = 3;

            // Sumcheck Prover
            let mut transcript = Transcript::<Fp>::default();
            let sc_proof = Sumcheck::prove::<U2>(claim, g.clone(), &mut transcript).unwrap();

            // Sumcheck Verifier
            let mut transcript = Transcript::<Fp>::default();
            let res = sc_proof
                .verify::<U2>(claim, degree_bound, num_rounds, g.clone(), &mut transcript)
                .unwrap();
            assert!(res);

            // Test invalid number of Unipolys
            let mut new_uni_polys = sc_proof.clone().polys;
            new_uni_polys.append(&mut vec![UniPoly::<Fp> {
                coeffs: vec![Fp::ONE, Fp::ONE],
            }]);
            let new_sc_proof = Sumcheck {
                polys: new_uni_polys,
            };
            let res = new_sc_proof.verify::<U2>(
                claim,
                degree_bound,
                num_rounds,
                g.clone(),
                &mut transcript,
            );
            assert_eq!(res.unwrap_err(), SumcheckError::InvalidUniPolys);

            // Test invalid degree bound
            let mut new_uni_polys = sc_proof.clone().polys;
            new_uni_polys[0] = UniPoly::<Fp> {
                coeffs: vec![Fp::ONE, Fp::ONE, Fp::ONE, Fp::ONE, Fp::ONE],
            };
            let new_sc_proof = Sumcheck {
                polys: new_uni_polys,
            };
            let res = new_sc_proof.verify::<U2>(
                claim,
                degree_bound,
                num_rounds,
                g.clone(),
                &mut transcript,
            );
            assert_eq!(res.unwrap_err(), SumcheckError::InvalidDegree);

            // Test false claim
            let false_claim = Fp::random(rand::thread_rng());
            let res = sc_proof.verify::<U2>(
                false_claim,
                degree_bound,
                num_rounds,
                g.clone(),
                &mut transcript,
            );
            assert_eq!(res.unwrap_err(), SumcheckError::InvalidClaim);
        }

        {
            // g(X0, X1, X2) = X0 * X1 + X1 * X2 + X2 * X0
            let term0 = Term(vec![(0, 1), (1, 1)]);
            let term1 = Term(vec![(1, 1), (2, 1)]);
            let term2 = Term(vec![(2, 1), (0, 1)]);
            let g = MultiPoly {
                num_vars: 3,
                terms: vec![(Fp::ONE, term0), (Fp::ONE, term1), (Fp::ONE, term2)],
            };
            let claim = Fp::from(6u64);
            let num_rounds = 3;
            let degree_bound = 1;

            // Sumcheck Prover
            let mut transcript = Transcript::<Fp>::default();
            let sc_proof = Sumcheck::prove::<U2>(claim, g.clone(), &mut transcript).unwrap();

            // Sumcheck Verifier
            let mut transcript = Transcript::<Fp>::default();
            let res = sc_proof
                .verify::<U2>(claim, degree_bound, num_rounds, g.clone(), &mut transcript)
                .unwrap();
            assert!(res);
        }
    }
}
