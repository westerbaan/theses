# Sampled re-audit of the paper formalisations, 2026-09-26

80 rows graded `ok` (proof faithful/route/mild/none), seed 20260926, over all six papers.  Regrade each from the paper's source and the Lean; findings go in `docs/audit/papers-sample-2026-09-26/`.

| file | line | DISP | lean_name | proof |
|---|---|---|---|---|
| papers-eja.csv | 10 | EJA 8 | `ejaU_eq_L` | none |
| papers-eja.csv | 15 | EJA 11 | `idem_Q_idem` | route |
| papers-eja.csv | 20 | EJA 16 | `IsFilter` | none |
| papers-eja.csv | 27 | EJA 23 | `floor_one` | faithful |
| papers-eja.csv | 32 | EJA 9 | `ejaU_bijective_iff` | none |
| papers-eja.csv | 35 | EJA 29 | `eja_im` | route |
| papers-eja.csv | 50 | EJA 27 | `polardecomp` | route |
| papers-eja.csv | 59 | EJA 34 | `Eja34Literal, PureRootHyp, eja34Literal_of_pureRoot` | none |
| papers-eja.csv | 68 | EJA 47 | `selfduality` | faithful |
| papers-eja.csv | 72 | EJA 51 | `dircomplete, state_normal, dircomplete_aux` | faithful |
| papers-fds.csv | 3 | FDS 2.1 | `StarCategory` | none |
| papers-fds.csv | 5 | FDS 2.2 | `CStarCategory` | none |
| papers-fds.csv | 19 | FDS 3.4 | `BanFunctor.Representation` | none |
| papers-fds.csv | 22 | FDS 4.2 | `IsDirectSum` | none |
| papers-fds.csv | 23 | FDS 4.3 | `—` | none |
| papers-fds.csv | 27 | FDS 5.1 | `directsum_equiv` | faithful |
| papers-fds.csv | 33 | FDS 5.3 | `concrete_directsum` | faithful |
| papers-oap.csv | 2 | OAP 1 | `oap1_one_eq_orth_zero` | route |
| papers-oap.csv | 5 | OAP 1 | `eaPartialOrder` | none |
| papers-oap.csv | 9 | OAP 1 | `oap1_osub_unique` | route |
| papers-oap.csv | 13 | OAP 1 | `EAEmbedding.injective` | route |
| papers-oap.csv | 27 | OAP 6 | `oap6_commutative` | route |
| papers-oap.csv | 29 | OAP 6 | `oap6_booleanAlgebra` | route |
| papers-oap.csv | 34 | OAP 8 | `oap8_isIso_iff` | route |
| papers-oap.csv | 38 | OAP 12 | `leftCorner` | none |
| papers-oap.csv | 40 | OAP 12 | `cornerEffectMonoid` | route |
| papers-oap.csv | 73 | OAP 26 | `oap26_3` | faithful |
| papers-oap.csv | 81 | OAP 31 | `oap31` | route |
| papers-oap.csv | 88 | OAP 36 | `oap36` | faithful |
| papers-oap.csv | 92 | OAP 39 | `oap39_1` | faithful |
| papers-oap.csv | 99 | OAP 41 | `oap41_4` | faithful |
| papers-oap.csv | 106 | OAP 44 | `IsBooleanEM` | none |
| papers-oap.csv | 108 | OAP 45 | `oap45_inf` | faithful |
| papers-oap.csv | 120 | OAP 59 | `ousEA` | none |
| papers-oap.csv | 125 | OAP 60 | `oap60_directed` | mild |
| papers-oap.csv | 127 | OAP 61 | `oap61` | faithful |
| papers-oap.csv | 134 | OAP 66 | `basicallyDisconnected_of_relSup` | none |
| papers-oap.csv | 148 | OAP 72 | `(none: remark, cited)` | none |
| papers-rec.csv | 19 | REC 10 | `rec10_tot` | none |
| papers-rec.csv | 25 | REC 15 | `EffectMonoid.ofBiadditive` | none |
| papers-rec.csv | 30 | REC 20 | `prodEffectMonoid` | none |
| papers-rec.csv | 40 | REC 23 | `HasFilters` | none |
| papers-rec.csv | 51 | REC 29 | `rec29_scalar_action` | none |
| papers-rec.csv | 54 | REC 30 | `directedCompleteEA_iff_down` | none |
| papers-rec.csv | 55 | REC 30 | `DirectedCompleteEffectus` | none |
| papers-rec.csv | 57 | REC 32 | `rec32_completeBoolean` | none |
| papers-rec.csv | 83 | REC 72 | `IsRigid` | none |
| papers-rec.csv | 87 | REC 75 | `asrtSharp_idem` | faithful |
| papers-rec.csv | 101 | REC 37 | `IsOrthoalgebra` | none |
| papers-rec.csv | 107 | REC 40 | `rec40_orderInterval` | none |
| papers-rec.csv | 116 | REC 47 | `OUSState` | none |
| papers-sea.csv | 3 | SEA 2 | `(remark, no declaration)` | none |
| papers-sea.csv | 8 | SEA 5 | `(remark, no declaration)` | none |
| papers-sea.csv | 14 | SEA 11 | `DirectedComplete` | none |
| papers-sea.csv | 22 | SEA 17 | `seq_le_left` | faithful |
| papers-sea.csv | 25 | SEA 17 | `sea17_5` | faithful |
| papers-sea.csv | 32 | SEA 22 | `sea22_noNilpotents` | faithful |
| papers-sea.csv | 34 | SEA 24 | `sea24_centralSplit` | faithful |
| papers-sea.csv | 36 | SEA 26 | `commutant` | none |
| papers-sea.csv | 49 | SEA 33 | `(remark, no declaration)` | none |
| papers-sea.csv | 51 | SEA 35 | `SEA35` | none |
| papers-sea.csv | 60 | SEA 41 | `sea41` | faithful |
| papers-sea.csv | 71 | SEA 36 | `sea36_spectral_unconditional` | faithful |
| papers-sea.csv | 72 | SEA 37 | `dcem_sqrt_unconditional` | faithful |
| papers-sea.csv | 73 | SEA 37 | `sea37_sqrt_unconditional` | faithful |
| papers-sea.csv | 90 | SEA 51 | `sea51_division_unconditional` | faithful |
| papers-sea.csv | 93 | SEA 57 | `sea57_convex_tfae_unconditional, sea57_moreover_unconditiona` | faithful |
| papers-sea.csv | 95 | SEA 59 | `sea59_split_unconditional` | faithful |
| papers-sea.csv | 103 | SEA 67 | `sea67_convex_iff, hasCommutingHalves_corner` | faithful |
| papers-sig.csv | 5 | SIG 4 | `pproj` | none |
| papers-sig.csv | 17 | SIG 18 | `sigmaPAM_extends_omegaComplete` | mild |
| papers-sig.csv | 18 | SIG 19 | `pred_sigmaEffectAlgebra` | faithful |
| papers-sig.csv | 22 | SIG 23 | `unitInterval_isSigmaEffectMonoid` | none |
| papers-sig.csv | 24 | SIG 25 | `pred_isSigmaEffectModule` | none |
| papers-sig.csv | 37 | SIG 40 | `normalisation_tfae` | route |
| papers-sig.csv | 42 | SIG 45 | `trivial_of_scalars_trivial` | faithful |
| papers-sig.csv | 51 | SIG 43 | `noZeroDivisorsTheorem` | none |
| papers-sig.csv | 58 | SIG 49 | `powersetMorphism, powerset, OmegaBA.sigmaEffectus` | none |
| papers-sig.csv | 72 | SIG 58 | `sBase_isEquivalence` | route |
| papers-sig.csv | 76 | SIG 73 | `SigmaExtension.sig73` | mild |
