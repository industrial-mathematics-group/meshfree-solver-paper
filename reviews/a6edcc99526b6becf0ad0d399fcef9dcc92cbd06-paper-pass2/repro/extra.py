import sys, numpy as np
sys.path.insert(0, sys.argv[1])
import stencil_diagnostics as sd, aligned_flux_diagnostics as af
for n, seed in ((48, 42), (300, 7)):
    P, L = sd.make_cloud(n, 0.2, seed); idx, off, m = sd.neighbour_table(P, L, 2.5)
    R=2.5
    V = sd.shepard_volumes(idx, off, m, R, L*L)
    w0 = sd.weight(0.0, R); W = np.where(m, sd.weight((off**2).sum(-1), R), 0.0); V0 = 1/(w0+W.sum(1)); V0 = V0*L*L/V0.sum()
    Ve = np.full(len(P), L*L/len(P))
    cs = {}
    for q in (1,3):
        c = sd.derivative_weights(off, m, R, q, True); cs[q]=c
        sh, wsh = af.sign_mismatch(idx, m, c)
        print(n, q, f"signmismatch {100*sh:.3f}% weight {100*wsh:.3f}%")
        for nm, VV in (("shepard+sweep",V),("nosweep",V0),("equal",Ve)):
            print(n, q, nm, f"pair defect {100*sd.pair_defect(idx,m,c,VV):.2f}%")
        # dissipation coeff with geometric orientation: sign(x)*c ; negative ones vs mean |c|
        coef = np.sign(off)*c
        a = np.abs(c)[np.broadcast_to(m[...,None], c.shape)]
        neg = coef[(coef<0)&m[...,None]]
        if neg.size: print(n,q,f"neg share {neg.size/a.size:.4f}, most negative {neg.min():.4f}, mean|c| {a.mean():.4f}, ratio {-neg.min()/a.mean():.3f}; mean of neg {neg.mean():.4f}")
    rng = np.random.default_rng(seed + 1)
    qmix = np.where(rng.random(len(P)) < 0.5, 1, 3)
    cmix = np.where((qmix == 1)[:, None, None], cs[1], cs[3])
    for nm, VV in (("shepard+sweep",V),("equal",Ve)):
        print(n, "mixed", nm, f"{100*sd.pair_defect(idx,m,cmix,VV,mask=lambda i,j:qmix[i]!=qmix[j]):.2f}%")
