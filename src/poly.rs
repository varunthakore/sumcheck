use ff::Field;

// Reference Arkworks ark-poly: https://docs.rs/ark-poly/latest/ark_poly/polynomial/multivariate/struct.SparseTerm.html
// Monomial with each element of the form `(variable, power)`.
#[derive(Clone, Debug)]
pub struct Term(pub Vec<(usize, usize)>);

impl Term {
    // Evaluate monomial at point = [X_0, X_1,..., X_{v-1}]
    fn evaluate<F: Field>(&self, point: Vec<F>) -> F {
        self.0
            .iter()
            .map(|(var, pow)| point[*var].pow([*pow as u64]))
            .product()
    }

    // Convert the monomial to univariate polynomial with varaible X_j evaluated at point
    // example for `term = X_0^0 * X_1^1 * X_2^1`, point = [1, 1, 3] and j = 1
    // `output = 3 * X_1^1` i.e. [0, 3]
    fn eval_to_univariate<F: Field>(&self, j: usize, point: Vec<F>) -> UniPoly<F> {
        // Degree of X_j in the term
        let mut deg = 0_usize;
        for (var, pow) in self.0.iter() {
            if *var == j {
                deg = *pow;
                break;
            }
        }

        // Evaluate term at point
        let eval = &self.evaluate(point);

        // Output the univariate polynomial
        let mut new_coeff = vec![F::ZERO; deg + 1];
        new_coeff[deg] = *eval;
        UniPoly { coeffs: new_coeff }
    }
}

// Multivariate Polynomial
#[derive(Clone, Debug)]
pub struct MultiPoly<F: Field> {
    // number of variables
    pub num_vars: usize,

    // vector of monomials with coeffs
    pub terms: Vec<(F, Term)>,
}

impl<F: Field> MultiPoly<F> {
    // Evaluate mutivatiate polynomial at point
    pub fn evaluate(&self, point: Vec<F>) -> F {
        self.terms
            .iter()
            .map(|(coeff, term)| *coeff * term.evaluate(point.clone()))
            .sum()
    }

    // Convert from multivariate to univariate polynomial with varaible X_j evaluated at point
    // example for `g(X0, X1, X2) = 2 * (X0 ^ 3) + X0 * X2 + X1 * X2`, j = 0 and point = [1, 0, 0]
    // output is `g(X0, 0, 0) = 2 * (X0 ^ 3)` i.e. [0, 0, 0, 2]
    fn eval_to_univariate(&self, j: usize, point: Vec<F>) -> UniPoly<F> {
        let mut out = UniPoly::<F>::zero_poly();

        assert_eq!(point[j], F::ONE);

        for (coeff, term) in self.terms.clone() {
            let mut new_poly = term.eval_to_univariate(j, point.clone());
            new_poly = new_poly.mul(coeff);
            out = out.add(new_poly);
        }

        out
    }

    // Summation of multivariate polynomial over r and hypercube to get univariate polynomial with varaible X_j
    // example for `g(X0, X1, X2) = 2 * (X0 ^ 3) + X0 * X2 + X1 * X2` and j = 0
    // `output = 8 * (X0 ^ 3) + 2 * X0 + 1` i.e. [1, 2, 0, 8]
    pub fn to_univariate(&self, j: usize, r: Vec<F>) -> UniPoly<F> {
        let mut out = UniPoly::zero_poly();

        let n = self.num_vars - j - 1;

        for vec in hypercube::<F>(n) {
            let mut point = r[..j].to_vec();
            point.push(F::ONE);
            point.extend_from_slice(&vec);
            assert_eq!(point.len(), self.num_vars);

            let poly = self.eval_to_univariate(j, point);

            out = out.add(poly);
        }

        out
    }
}

// Univariate Polynomial
#[derive(Clone, Debug)]
pub struct UniPoly<F: Field> {
    // vector of coeffs
    // Polynomial "g = aX^3 + bX + c"  is stored as [c, b, 0, a]
    pub coeffs: Vec<F>,
}

impl<F: Field> UniPoly<F> {
    // Zero polynomial
    fn zero_poly() -> Self {
        UniPoly {
            coeffs: vec![F::ZERO],
        }
    }

    // degree
    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    // Evaluate the polynomial at 0
    pub fn evluate_at_zero(&self) -> F {
        self.coeffs[0]
    }

    // Evaluate the polynomial at 1
    pub fn evaluate_at_one(&self) -> F {
        self.coeffs.iter().sum()
    }

    // Evaluate the polynomial at x
    pub fn evaluate(&self, x: F) -> F {
        self.coeffs
            .iter()
            .enumerate()
            .fold(F::ZERO, |eval, (i, acc)| eval + *acc * x.pow([i as u64]))
    }

    // Multiply by Field element
    fn mul(&self, e: F) -> Self {
        let new_coeffs = self.coeffs.iter().map(|&coeff| coeff * e).collect();

        Self { coeffs: new_coeffs }
    }

    // Add two poly of unequal degree
    fn add(&self, other: UniPoly<F>) -> Self {
        let mut new_coeffs = vec![];

        for (x, y) in self.coeffs.iter().zip(&other.coeffs) {
            new_coeffs.push(*x + *y);
        }

        match self.coeffs.len().cmp(&other.coeffs.len()) {
            std::cmp::Ordering::Greater => {
                new_coeffs.extend_from_slice(&self.coeffs[other.coeffs.len()..]);
            }
            std::cmp::Ordering::Less => {
                new_coeffs.extend_from_slice(&other.coeffs[self.coeffs.len()..]);
            }
            std::cmp::Ordering::Equal => {
                // If Equal Do Nothing
            }
        }

        Self { coeffs: new_coeffs }
    }
}

// Get boolean hypercube of size 'n'
fn hypercube<F: Field>(n: usize) -> Vec<Vec<F>> {
    let mut vectors = vec![];
    for v in 0..(1 << n) {
        // let bits = (v as u64).to_le_bytes();
        let vector = (0..n)
            .rev()
            .map(|i| if (v & (1 << i)) != 0 { F::ZERO } else { F::ONE })
            .collect();
        vectors.push(vector);
    }
    vectors
}

#[cfg(test)]
mod test {

    use super::{MultiPoly, Term, UniPoly};
    use ff::Field;
    use pasta_curves::Fp;

    #[test]
    fn test_term() {
        // term0 = X0 ^ 3
        let term0 = Term(vec![(0, 3)]);

        // term1 = X0 * X2
        let term1 = Term(vec![(0, 1), (2, 1)]);

        // term2 = X1 * X2
        let term2 = Term(vec![(1, 1), (2, 1)]);

        // Test evaluate at [X0=1, X1=2, X2=3]
        assert_eq!(
            term0.evaluate(vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)]),
            Fp::from(1u64)
        );
        assert_eq!(
            term1.evaluate(vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)]),
            Fp::from(3u64)
        );
        assert_eq!(
            term2.evaluate(vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)]),
            Fp::from(6u64)
        );

        // Test to_univariate()
        assert_eq!(
            term0
                .eval_to_univariate(0, vec![Fp::from(1u64), Fp::from(2u64), Fp::from(3u64)])
                .coeffs,
            [Fp::ZERO, Fp::ZERO, Fp::ZERO, Fp::ONE]
        );
        assert_eq!(
            term1
                .eval_to_univariate(1, vec![Fp::from(1u64), Fp::from(1u64), Fp::from(3u64)])
                .coeffs,
            [Fp::from(3u64)]
        );
        assert_eq!(
            term2
                .eval_to_univariate(1, vec![Fp::from(1u64), Fp::from(1u64), Fp::from(3u64)])
                .coeffs,
            [Fp::ZERO, Fp::from(3u64)]
        );
    }

    #[test]
    fn test_multi() {
        // g(X0, X1, X2) = 2 * (X0 ^ 3) + X0 * X2 + X1 * X2
        let term0 = Term(vec![(0, 3)]);
        let term1 = Term(vec![(0, 1), (2, 1)]);
        let term2 = Term(vec![(1, 1), (2, 1)]);
        let g = MultiPoly {
            num_vars: 3,
            terms: vec![(Fp::from(2u64), term0), (Fp::ONE, term1), (Fp::ONE, term2)],
        };

        // Test evaluate()
        assert_eq!(
            g.evaluate(vec![Fp::from(2u64), Fp::from(3u64), Fp::from(6u64)]),
            Fp::from(46u64)
        );

        // Test eval_to_univariate()
        assert_eq!(
            g.eval_to_univariate(0, vec![Fp::ONE, Fp::ZERO, Fp::ZERO])
                .coeffs,
            [Fp::ZERO, Fp::ZERO, Fp::ZERO, Fp::from(2u64)]
        );
        assert_eq!(
            g.eval_to_univariate(0, vec![Fp::ONE, Fp::ZERO, Fp::ONE])
                .coeffs,
            [Fp::ZERO, Fp::ONE, Fp::ZERO, Fp::from(2u64)]
        );
        assert_eq!(
            g.eval_to_univariate(0, vec![Fp::ONE, Fp::ONE, Fp::ZERO])
                .coeffs,
            [Fp::ZERO, Fp::ZERO, Fp::ZERO, Fp::from(2u64)]
        );
        assert_eq!(
            g.eval_to_univariate(0, vec![Fp::ONE, Fp::ONE, Fp::ONE])
                .coeffs,
            [Fp::ONE, Fp::ONE, Fp::ZERO, Fp::from(2u64)]
        );

        // Test to_univariate
        assert_eq!(
            g.to_univariate(0, vec![Fp::ZERO]).coeffs,
            vec![Fp::ONE, Fp::from(2u64), Fp::ZERO, Fp::from(8u64)]
        );
        assert_eq!(
            g.to_univariate(1, vec![Fp::from(2u64)]).coeffs,
            vec![Fp::from(34u64), Fp::ONE]
        );
        assert_eq!(
            g.to_univariate(2, vec![Fp::from(2u64), Fp::from(3u64)])
                .coeffs,
            vec![Fp::from(16u64), Fp::from(5u64)]
        );
    }

    #[test]
    fn test_uni() {
        // p = 8 * X^3 + 2 * X + 1
        let p = UniPoly {
            coeffs: vec![Fp::ONE, Fp::from(2u64), Fp::ZERO, Fp::from(8u64)],
        };

        // Test evluate_at_zero()
        assert_eq!(p.evluate_at_zero(), Fp::ONE);

        // Test evaluate_at_one()
        assert_eq!(p.evaluate_at_one(), Fp::from(11u64));

        // Test evaluate()
        assert_eq!(p.evaluate(Fp::from(2u64)), Fp::from(69u64));
    }
}
