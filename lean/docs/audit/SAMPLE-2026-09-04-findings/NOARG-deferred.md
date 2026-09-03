
## faithful_check NOARG leads outside this worker's editable set (2026-09-04)

Decisions re-derived from the .tex sources, not from the rows' own notes.
Apply the sentence verbatim as the prefix of the `status` field
(`regraded 2026-09-04: <sentence>. `) and set `proof` to `none` for every
row marked `-> none`.  Rows marked `stands` need no edit.

### acstar-positive.csv

acstar-positive.csv:37 16VII gelfand_mazur -> stands
The Theorem itself prints no proof, but the exercise point immediately above it (cstar.tex:2670-2672, "Use the previous exercise to prove the following theorem") carries a full solution at asols.tex:1910-1920, keyed `parsec-160.61`, which proves exactly this statement; the check missed it because the solution hangs off the neighbouring exercise, not off 160.70.

acstar-positive.csv:100 21II OrderSeparating.separating -> none
the point prints no argument -- 21II `separating` is a Definition (cstar.tex:3113-3154) whose closing parenthetical "(Note that (1) => (2) => (3) => (4).)" asserts the three implications without a word of proof -- so there is nothing for faithful to match

acstar-positive.csv:101 21II Separating.faithful -> none
the point prints no argument -- 21II `separating` is a Definition (cstar.tex:3113-3154) whose closing parenthetical "(Note that (1) => (2) => (3) => (4).)" asserts the three implications without a word of proof -- so there is nothing for faithful to match

acstar-positive.csv:102 21II Faithful.centreSeparating -> none
the point prints no argument -- 21II `separating` is a Definition (cstar.tex:3113-3154) whose closing parenthetical "(Note that (1) => (2) => (3) => (4).)" asserts the three implications without a word of proof -- so there is nothing for faithful to match

### aproc-duplicators-quantumlambda.csv

aproc-duplicators-quantumlambda.csv:47 130V discrete_ell_x -> none
the point prints no argument -- 130V `cor:discrete-ell-x` is a bare Corollary (proc.tex:6531-6535), four lines of statement with no proof point and no printed derivation from 130IV and 130II (the "combine 130IV with 130II" of the row's note is the auditor's reconstruction, not printed text) -- so there is nothing for faithful to match

aproc-duplicators-quantumlambda.csv:50 132III dup_vna_is_monoid_1 -> none
the point prints no argument -- clause 1 of the Exercise `prop:dup-vna-is-monoid` (proc.tex:6686-6689) is a bare "Show that any monoid structure on A in W*cpsu is a duplicator on A", with no hint and no solution (asols.tex carries nothing past parsec 340) -- so there is nothing for faithful to match

aproc-duplicators-quantumlambda.csv:52 132III dup_vna_is_monoid_2 -> stands
Clause 2 prints its route: "Deduce from this and \sref{duplicable} that ..." (proc.tex:6690-6702) names both inputs, and the row records that the proof takes them.

aproc-duplicators-quantumlambda.csv:53 132III dup_vna_is_monoid_3 -> none
the point prints no argument -- clause 3 of the Exercise `prop:dup-vna-is-monoid` (proc.tex:6703-6707) is a bare "Show that the monoid morphisms in W*miu and in W*cpsu are precisely the nmiu-maps", with no hint and no solution -- so there is nothing for faithful to match

aproc-duplicators-quantumlambda.csv:54 132III dup_vna_is_monoid_4 -> stands
Clause 4 is printed as "Conclude that CMon(W*miu) = Mon(W*miu) = CMon(W*cpsu) = Mon(W*cpsu)" (proc.tex:6708-6713); inside an enumerated exercise "Conclude" directs at the preceding clauses, and the row's note records that the proof runs through parts 3 and 4. (Weakest of the "printed directive" set -- flagging it in case the orchestrator draws the line tighter.)

aproc-duplicators-quantumlambda.csv:55 132III dup_vna_is_monoid_5 -> stands
Clause 5 carries a printed Hint (proc.tex:6720-6721, "l^inf : Set -> (W*miu)^op is full and faithful by cor:linf-ff"), which the row says is the proof followed.

aproc-duplicators-quantumlambda.csv:81 122VI cor_linf_ff_1 -> stands
The Exercise opens "Deduce from \sref{nmiu-functional-product} that ..." (proc.tex:4618-4624), a printed directive naming the input; the row already records that this is the whole of the author's argument and that it is followed.

aproc-duplicators-quantumlambda.csv:82 122VI cor_linf_ff_2 -> stands
Same printed directive: eta being a bijection is the second half of the "Deduce from nmiu-functional-product" sentence (proc.tex:4622-4624).

### aproc-tensor.csv

aproc-tensor.csv:13 109III hilbertTensor_nonempty -> stands
Clause 3 prints its route -- "(using the fact that every Hilbert space has an orthonormal basis)" (proc.tex:2146-2147) on top of clauses 1 and 2 of the same exercise, which are built for it; the row records that the proof now takes exactly that route.

aproc-tensor.csv:33 111XII isTensorProduct_comp -> stands
The Exercise is "construct a tensor product ... using \sref{ngns} and \sref{special-tensor}" (proc.tex:2589-2596): the two named inputs are the printed argument, and this declaration is the transport they need.

aproc-tensor.csv:34 111XII vnTensorProduct_exists -> stands
Same printed directive "using \sref{ngns} and \sref{special-tensor}" (proc.tex:2589-2596).

aproc-tensor.csv:35 111XII vnTensorProduct_nonempty -> stands
Same printed directive "using \sref{ngns} and \sref{special-tensor}" (proc.tex:2589-2596).

aproc-tensor.csv:48 112V basic_state_inner_product -> stands
The Exercise is "Use \sref{product-state-positive} to show that [.,.]_omega ... is an inner product" (proc.tex:2814-2820) -- a printed instruction naming the input.

aproc-tensor.csv:58 112IX product_functional -> stands
The Exercise prints "(perhaps using \sref{luws})" (proc.tex:2872), and the row records that the proof follows that hint.

### avn-basic.csv

avn-basic.csv:65 44XI nonneg_of_conjNP -> stands
The Exercise prints "using \sref{proto-gelfand-naimark}" (vn.tex:755-760) for exactly this preliminary claim, and the row records that the proof follows it.

avn-basic.csv:66 44XI np_orderSeparating -> stands
Same printed directive: "Show that the set of np-functionals ... is not only faithful but also order separating using \sref{proto-gelfand-naimark}" (vn.tex:755-760).

avn-basic.csv:84 45IV mult_uws_cont_ad -> stands
The Exercise prints "Conclude (using \sref{cp-uscont} and \sref{ad-cp}) that a -> b*ab is ultrastrongly continuous" (vn.tex:867-872) -- both inputs named; the row records the repair that made the proof take them.

avn-basic.csv:85 45IV mult_uws_cont -> stands
Second half of the same Exercise: "Use this, and \sref{mult-polarization}, to show that b -> ab, ba are ultraweakly and ultrastrongly continuous" (vn.tex:874-879).

avn-basic.csv:125 51IX Linfty_vn -> none
the point prints no argument -- 51IX `Linfty-vn` is a bare Corollary (vn.tex:1637-1644), seven lines of statement with no proof point and no printed derivation from 51VII -- so there is nothing for faithful to match

avn-basic.csv:126 51IX instVonNeumannAlgebra -> none
the point prints no argument -- 51IX `Linfty-vn` is a bare Corollary (vn.tex:1637-1644) with no proof point and no printed derivation from 51VII -- so there is nothing for faithful to match

avn-basic.csv:127 51IX integralNP -> none
the point prints no argument -- 51IX `Linfty-vn` is a bare Corollary (vn.tex:1637-1644) with no proof point and no printed derivation from 51VII -- so there is nothing for faithful to match

avn-basic.csv:132 52III meagre_basic_3 -> stands
Clause 3 carries a printed Hint (vn.tex:1749-1750, "show that closure(U) minus U is closed with empty interior"), which the row records as the proof followed.

### avn-division-normalfunctionals.csv

avn-division-normalfunctionals.csv:3 79I isPseudoinverse_unique -> none
the point prints no argument -- 79I `dfn-pseudoinverse` is a Definition (vn.tex:5089-5107) and its uniqueness clause is the parenthetical bare citation "(by \sref{mult-cancellation})" -- so there is nothing for faithful to match

avn-division-normalfunctionals.csv:216 21II gnsRepOn_injective -> none
the point prints no argument -- 21II `separating` is a Definition (cstar.tex:3113-3154) and prints nothing but its four clauses and the parenthetical implication chain -- so there is nothing for faithful to match
(Flag for the orchestrator: this row's DISP looks mis-keyed as well. Its note says the declaration is "not a point of parsec 900" but the injectivity of rho_Omega that parsec 900 opens with, taken from cstar 30X; if the DISP is re-keyed to 30X the grade should be re-derived against 30X's printed proof rather than against 21II.)

### bdils-paschke-stinespring.csv

bdils-paschke-stinespring.csv:7 154II norm_sq_sum_ptprod -> stands
The identity is printed AND derived inside the thesis's own proof: 154V, the first step of the Proof of 154III (dils.tex:3644-3650, "By definition we have ||sum a_i (x) b_i||^2 = ... = ||sum b_i* phi(a_i* a_j) b_j||"). The DISP names the Definition 154II, which by itself prints nothing -- the row's note already says so -- but the argument is printed one point later, so the grade is right; only the DISP is arguably off.

bdils-paschke-stinespring.csv:8 154II paschkeModule_norm_sq_sum_tprod -> stands
Same: derived in the printed proof at 154V (dils.tex:3644-3650).

bdils-paschke-stinespring.csv:52 135IV stinespring_aux -> stands
135IV `stinespring-theorem` prints no proof in place, but points forward at dils.tex:35 ("We will see a detailed proof later, in \sref{dils-proof-stinespring}") to the thesis's own full proof at 137II (dils.tex:399, titled "Proof of Stinespring's theorem, \sref{stinespring-theorem}"). That is the printed argument, and the row records that it is what is transcribed.

bdils-paschke-stinespring.csv:53 135IV stinespring_normal_aux -> stands
Same printed proof at 137II (dils.tex:399 ff.); the normality clause is settled there and at 139I.

bdils-paschke-stinespring.csv:54 135IV stinespring -> stands
Same printed proof at 137II (dils.tex:399 ff.).

bdils-paschke-stinespring.csv:55 135IV stinespring_unital -> stands
Same printed proof at 137II (dils.tex:399 ff.).

bdils-paschke-stinespring.csv:56 135IV stinespring_normal -> stands
Same printed proof at 137II (dils.tex:399 ff.).

### bdils-selfdual-kaplansky.csv

bdils-selfdual-kaplansky.csv:101 158Ia kaplansky_bounded_approx -> none
the point prints no argument -- 158Ia (dils.tex:4129-4136) is an untitled restatement of the classical Kaplansky density theorem, quoted as background for the generalization that follows, with no proof point and nothing but the bare "Cf. \sref{kaplansky}" of the next point -- so there is nothing for faithful to match

### Note on the status wording (applies to every `-> none` row above)

The bare prefix `regraded 2026-09-04: ` makes `sorry_map.py --conflicts` report
the row under NOVERDICT whenever the rest of the status field carries no verdict
of its own (which is the usual case: these rows had an empty status).  `regraded`
is not in the closed verdict vocabulary and the fallback reads it as a category.
Rows whose existing status already names a verdict (`repaired`, `left-benign`,
`left-thesis`, ...) are unaffected -- `verdict_of` scans in table order, so the
old verdict still wins.

This worker's own 30 rows therefore use

    regraded 2026-09-04: reclassified faithful -> none. <sentence>. <old field>

`reclassified` is in the vocabulary and folds to `repaired`, which is what a
corrected grade is; `verdict_conflicts` stays at one match, so no AMBIG is
created.  Recommend the same shape for the rows above, adding
`reclassified faithful -> none. ` only where the existing status field is empty
or carries no verdict.
