import { readFileSync, writeFileSync } from 'node:fs';

const dir = new URL('.', import.meta.url);

const notes = {
  basic: {
    uniformApproxErrorAbs_eq_sSup: 'For [a real polynomial](hyp:p), [its uniform absolute-value approximation error is the supremum of its pointwise residual on the unit interval](goal).',
    uniformApproxErrorAbs_le_iff: 'For [a real polynomial](hyp:p) and [a proposed error bound](hyp:e), [the bound holds exactly when it bounds every residual on the unit interval](goal).',
    bestUniformApproxErrorAbs_eq_sInf: 'For [a polynomial degree limit](hyp:K), [the best absolute-value approximation error is the infimum over all admissible polynomial errors](goal).',
    bestUniformApproxErrorAbs_nonneg: 'For [a polynomial degree limit](hyp:K), [the best approximation error cannot be negative](goal).',
    bestUniformApproxErrorAbs_antitone: 'For [two degree limits with the first no larger than the second](hyp:K,L,hKL), [allowing the larger degree cannot increase the best error](goal).',
    exists_bestPolynomialAbs: 'For [a polynomial degree limit](hyp:K), [some admissible polynomial attains the best absolute-value approximation error](goal).',
    exists_bestPolynomialAbs_interval: 'For [a polynomial degree limit](hyp:K), [some admissible polynomial bounds every absolute-value residual by the best error on the unit interval](goal).',
    bestUniformApproxErrorAbs_two_mul_add_one: 'For [a nonnegative integer](hyp:m), [allowing the odd degree 2m+1 gives the same best error as degree 2m](goal).'
  },
  fejer: {
    continuous_fejerKernel: 'For [a Fejér order](hyp:n), [the normalized Fejér kernel is continuous](goal).',
    integral_fourier: 'For [a Fourier frequency](hyp:k), [its Haar integral is one at frequency zero and zero otherwise](goal).',
    fejer_integrand_expand: 'For [a Fejér order, Fourier frequency, and circle point](hyp:n,k,t), [the kernel-weighted character has the stated finite Fourier expansion](goal).',
    fejerMean_fourier_nat: 'For [a positive Fejér order](hyp:n,hn) and [a nonnegative frequency](hyp:k), [the Fejér mean has the stated triangular multiplier](goal).',
    fejerMean_fourier_neg_nat: 'For [a positive Fejér order](hyp:n,hn) and [a negative frequency magnitude](hyp:k), [the Fejér mean has the same triangular multiplier](goal).',
    integral_fejerKernel: 'For [a positive Fejér order](hyp:n,hn), [the normalized kernel integrates to one](goal).',
    fejerMean_norm_le: 'For [a positive Fejér order](hyp:n,hn), [a continuous input](hyp:f), and [a uniform norm bound](hyp:E,hE), [the Fejér mean obeys that bound](goal).',
    fejerMeanCLM_apply: 'For [a positive Fejér order](hyp:n,hn) and [a continuous input](hyp:f), [the packaged linear map equals the integral definition](goal).',
    valleePoussinMean_fourier_nat: 'For [a positive order](hyp:n,hn) and [a frequency at most that order](hyp:k,hk), [the de la Vallée--Poussin mean preserves the nonnegative Fourier character](goal).',
    valleePoussinMean_fourier_neg_nat: 'For [a positive order](hyp:n,hn) and [a frequency magnitude at most that order](hyp:k,hk), [the de la Vallée--Poussin mean preserves the negative Fourier character](goal).',
    cuspFunctional_fourier_nat: 'For [a positive order](hyp:n,hn) and [a nonnegative frequency at most that order](hyp:k,hk), [the cusp functional annihilates the Fourier character](goal).',
    cuspFunctional_fourier_neg_nat: 'For [a positive order](hyp:n,hn) and [a negative frequency magnitude at most that order](hyp:k,hk), [the cusp functional annihilates the Fourier character](goal).',
    cuspFunctional_fourier_nat_nonneg: 'For [a positive order](hyp:n,hn) and [a nonnegative frequency](hyp:k), [the real part of the cusp multiplier is nonnegative](goal).',
    cuspFunctional_fourier_neg_nat_nonneg: 'For [a positive order](hyp:n,hn) and [a negative frequency magnitude](hyp:k), [the real part of the cusp multiplier is nonnegative](goal).',
    cuspFunctional_fourier_nat_high: 'For [a positive order](hyp:n,hn) and [a nonnegative frequency at least twice that order](hyp:k,hk), [the cusp functional has multiplier one](goal).',
    cuspFunctional_fourier_neg_nat_high: 'For [a positive order](hyp:n,hn) and [a negative frequency magnitude at least twice that order](hyp:k,hk), [the cusp functional has multiplier one](goal).',
    cuspFunctional_norm_apply_le: 'For [a positive order](hyp:n,hn) and [a continuous input](hyp:f), [the cusp functional is bounded by four times the uniform norm](goal).',
    fourier_pair_eq: 'For [two real coefficients, a frequency, and a circle coordinate](hyp:A,B,k,t), [the conjugate Fourier pair equals the corresponding real sine--cosine mode](goal).',
    exists_fourierPoly_sinDouble: 'For [a polynomial of degree at most a positive order](hyp:p,n,hn,hp), [there is a corresponding Fourier polynomial that agrees after sine composition and is annihilated by the cusp functional](goal).',
    fourier_comp_circleDouble: 'For [a Fourier frequency](hyp:j), [composition with circle doubling doubles that frequency](goal).'
  },
  duality: {
    exists_absExtremalDecomposition: 'For [a polynomial degree limit](hyp:K), [a normalized extremal signed-measure decomposition exists](goal).',
    exists_symmetric_momentMatched_absGap: 'For [a positive even degree](hyp:K,_hK,_hEven), [a symmetric moment-matched probability-prior pair with the exact absolute-moment gap exists](goal).',
    priorZero_isProbabilityMeasure: 'For [a packaged prior pair](hyp:K,P), [its first prior is a probability measure](goal).',
    priorOne_isProbabilityMeasure: 'For [a packaged prior pair](hyp:K,P), [its second prior is a probability measure](goal).',
    priorZero_mass: 'For [a packaged prior pair](hyp:K,P), [its first prior has total mass one](goal).',
    priorOne_mass: 'For [a packaged prior pair](hyp:K,P), [its second prior has total mass one](goal).',
    priorZero_supported: 'For [a packaged prior pair](hyp:K,P), [its first prior is supported on the unit interval](goal).',
    priorOne_supported: 'For [a packaged prior pair](hyp:K,P), [its second prior is supported on the unit interval](goal).',
    priorZero_symmetric: 'For [a packaged prior pair](hyp:K,P), [its first prior is symmetric about zero](goal).',
    priorOne_symmetric: 'For [a packaged prior pair](hyp:K,P), [its second prior is symmetric about zero](goal).',
    prior_moments_eq: 'For [a packaged prior pair](hyp:K,P) and [a moment order no larger than the degree limit](hyp:j,hj), [the two priors have equal moments of that order](goal).',
    prior_absMoment_gap: 'For [a packaged prior pair](hyp:K,P), [the oriented difference in absolute first moments is twice the best approximation error](goal).'
  },
  rate: {
    bestUniformApproxErrorAbs_upper: 'For [a positive polynomial degree](hyp:K,hK), [the best absolute-value approximation error is at most one divided by that degree](goal).',
    bestUniformApproxErrorAbs_lower: 'For [a positive polynomial degree](hyp:K,hK), [the cusp of absolute value forces the stated inverse-degree lower bound](goal).',
    bestUniformApproxErrorAbs_order: '[There are universal positive constants](goal) that sandwich the best absolute-value approximation error between constant multiples of the reciprocal degree for every positive degree.'
  }
};

for (const [stem, decls] of Object.entries(notes)) {
  const path = new URL(`${stem}.lean`, dir);
  let text = readFileSync(path, 'utf8');
  for (const [name, sentence] of Object.entries(decls)) {
    const re = new RegExp(`(/--(?:(?!-/)[\\s\\S])*-/)(\\n(?:@\\[[^\\n]*\\] )?(?:theorem|lemma) ${name}\\b)`);
    if (!re.test(text)) throw new Error(`missing documentation for ${stem}.${name}`);
    text = text.replace(re, (_, doc, decl) => `${doc.slice(0, 3)} ${sentence}\n\n${doc.slice(3)}${decl}`);
  }
  writeFileSync(path, text);
}
