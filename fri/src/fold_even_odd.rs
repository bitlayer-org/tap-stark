use alloc::vec::Vec;

use itertools::Itertools;
use p3_field::TwoAdicField;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use tracing::instrument;

/// Fold a polynomial
/// ```ignore
/// p(x) = p_even(x^2) + x p_odd(x^2)
/// ```
/// into
/// ```ignore
/// p_even(x) + beta p_odd(x)
/// ```
/// Expects input to be bit-reversed evaluations.
#[instrument(skip_all, level = "debug")]
pub fn fold_even_odd<F: TwoAdicField>(poly: Vec<F>, beta: F) -> Vec<F> {
    // We use the fact that
    //     p_e(x^2) = (p(x) + p(-x)) / 2
    //     p_o(x^2) = (p(x) - p(-x)) / (2 x)
    // that is,
    //     p_e(g^(2i)) = (p(g^i) + p(g^(n/2 + i))) / 2
    //     p_o(g^(2i)) = (p(g^i) - p(g^(n/2 + i))) / (2 g^i)
    // so
    //     result(g^(2i)) = p_e(g^(2i)) + beta p_o(g^(2i))
    //                    = (1/2 + beta/2 g_inv^i) p(g^i)
    //                    + (1/2 - beta/2 g_inv^i) p(g^(n/2 + i))
    let m = RowMajorMatrix::new(poly, 2);
    let g_inv = F::two_adic_generator(log2_strict_usize(m.height()) + 1).inverse();
    let one_half = F::two().inverse();
    let half_beta = beta * one_half;

    // TODO: vectorize this (after we have packed extension fields)

    // beta/2 times successive powers of g_inv
    let mut powers = g_inv
        .shifted_powers(half_beta)
        .take(m.height())
        .collect_vec();
    reverse_slice_index_bits(&mut powers);

    m.par_rows()
        .zip(powers)
        .map(|(mut row, power)| {
            let (r0, r1) = row.next_tuple().unwrap();
            (one_half + power) * r0 + (one_half - power) * r1
        })
        .collect()
}

#[cfg(test)]
mod tests {

    use itertools::izip;
    use p3_baby_bear::BabyBear;
    use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
    use p3_field::extension::BinomialExtensionField;
    use p3_field::AbstractExtensionField;
    use primitives::field::BfField;
    use rand::{thread_rng, Rng};
    use scripts::execute_script;
    use scripts::u31_lib::BabyBear4;

    use super::*;
    use crate::fri_scripts::verify_folding::fold_degree;

    #[test]
    fn test_fold_even_odd() {
        type F = BabyBear;

        let mut rng = thread_rng();

        let log_n = 10;
        let n = 1 << log_n;
        let coeffs = (0..n).map(|_| rng.gen::<F>()).collect::<Vec<_>>();

        let dft = Radix2Dit::default();
        let evals = dft.dft(coeffs.clone());

        let even_coeffs = coeffs.iter().cloned().step_by(2).collect_vec();
        let even_evals = dft.dft(even_coeffs);

        let odd_coeffs = coeffs.iter().cloned().skip(1).step_by(2).collect_vec();
        let odd_evals = dft.dft(odd_coeffs);

        let beta = rng.gen::<F>();
        let expected = izip!(even_evals, odd_evals)
            .map(|(even, odd)| even + beta * odd)
            .collect::<Vec<_>>();

        // fold_even_odd takes and returns in bitrev order.
        let mut folded = evals;
        reverse_slice_index_bits(&mut folded);
        folded = fold_even_odd(folded, beta);
        reverse_slice_index_bits(&mut folded);

        assert_eq!(expected, folded);
    }

    #[test]
    fn test_fold_even_odd_1() {
        type F = BabyBear;

        let log_n = 4;
        let n = 1 << log_n;
        let coeffs = (0..n).map(|i: u32| F::from_u32(i)).collect::<Vec<_>>();

        let dft = Radix2Dit::default();
        let evals = dft.dft(coeffs.clone());

        let even_coeffs = coeffs.iter().cloned().step_by(2).collect_vec();
        let even_evals = dft.dft(even_coeffs);

        let odd_coeffs = coeffs.iter().cloned().skip(1).step_by(2).collect_vec();
        let odd_evals = dft.dft(odd_coeffs);

        let beta = F::from_u32(2);
        let expected = izip!(even_evals, odd_evals)
            .map(|(even, odd)| even + beta * odd)
            .collect::<Vec<_>>();

        print!("{:?}", expected);
        print!("{:?}", evals);
        // fold_even_odd takes and returns in bitrev order.
        let mut folded = evals;
        reverse_slice_index_bits(&mut folded);
        folded = fold_even_odd(folded, beta);
        reverse_slice_index_bits(&mut folded);

        assert_eq!(expected, folded);
    }

    #[test]
    fn test_fold_bitcoin_script() {
        use p3_field::AbstractField;
        type AF = BabyBear;
        type F = BinomialExtensionField<BabyBear, 4>;

        let mut rng = thread_rng();
        let log_n = 4;
        let n = 1 << log_n;
        let coeffs = (0..n)
            .map(|i: u32| F::from_base_fn(|_i| rng.gen::<F>()))
            .collect::<Vec<_>>();

        let dft = Radix2Dit::default();
        let evals = dft.dft(coeffs.clone());

        let even_coeffs = coeffs.iter().cloned().step_by(2).collect_vec();
        let even_evals = dft.dft(even_coeffs);

        let odd_coeffs = coeffs.iter().cloned().skip(1).step_by(2).collect_vec();
        let odd_evals = dft.dft(odd_coeffs);

        let beta = F::from_base_slice(vec![AF::from_canonical_u32(2); 4].as_slice());
        let expected = izip!(even_evals, odd_evals)
            .map(|(even, odd)| even + beta * odd)
            .collect::<Vec<_>>();

        println!("{:?}", evals);
        println!("------- folding -------");
        println!("{:?}", expected);

        // fold_even_odd takes and returns in bitrev order.
        let mut folded = evals.clone();
        reverse_slice_index_bits(&mut folded);
        folded = fold_even_odd(folded, beta);
        reverse_slice_index_bits(&mut folded);

        assert_eq!(expected, folded);

        for (_index, log_n) in vec![4].iter().enumerate() {
            let n = 1 << log_n;
            let y0 = evals.clone();
            let y1 = expected.clone();

            let subgroup_generator = F::two_adic_generator(*log_n);

            for j in 0..n as usize {
                let x_index = j;
                let x_nge_index = (n / 2 + x_index) % n;
                let x = subgroup_generator.exp_u64(x_index as u64);
                let y0_x = y0[x_index];
                let y0_neg_x = y0[x_nge_index];
                let y_1_x_quare = y1[x_index % (n / 2)];

                let with_input_script = fold_degree::<F>(
                    x.as_u32_vec(),
                    y0_x.as_u32_vec(),
                    y0_neg_x.as_u32_vec(),
                    beta.as_u32_vec(),
                    y_1_x_quare.as_u32_vec(),
                    true,
                );
                let result = execute_script(with_input_script);
                println!("{:?}", result);
                assert!(result.success);

                // let script = fold_degree::<F>(
                //     x.as_u32_vec(),
                //     y0_x.as_u32_vec(),
                //     y0_neg_x.as_u32_vec(),
                //     beta.as_u32_vec(),
                //     y_1_x_quare.as_u32_vec(),
                //     false,
                // );
                // let result = execute_script(script);
                // assert!(result.success);
            }
        }
    }
}
