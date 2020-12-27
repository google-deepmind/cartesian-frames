(*
Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

open HolKernel boolLib bossLib boolSimps Parse dep_rewrite
  sortingTheory pred_setTheory listTheory relationTheory stringTheory cf0Theory

val _ = new_theory"matrix";

(* TODO: move *)
Theorem GENLIST_EQ_NIL[simp]:
  !n. GENLIST f n = [] <=> n = 0
Proof
  Cases \\ rw[GENLIST]
QED

Theorem nub_GENLIST:
  nub (GENLIST f n) =
    MAP f (FILTER (\i. !j. (i < j) /\ (j < n) ==> f i <> f j) (COUNT_LIST n))
Proof
  simp[rich_listTheory.COUNT_LIST_GENLIST]
  \\ qid_spec_tac`f`
  \\ Induct_on`n` \\ simp[]
  \\ simp[GENLIST_CONS]
  \\ simp[nub_def]
  \\ gen_tac
  \\ simp[MEM_GENLIST]
  \\ qmatch_goalsub_abbrev_tac`COND b1`
  \\ qmatch_goalsub_abbrev_tac`MAP f (COND b2 _ _)`
  \\ qmatch_goalsub_abbrev_tac`f 0 :: r1`
  \\ qmatch_goalsub_abbrev_tac`0 :: r2`
  \\ `b2 = ~b1`
  by (
    rw[Abbr`b1`, Abbr`b2`, EQ_IMP_THM]
    >- (
      CCONTR_TAC \\ fs[]
      \\ first_x_assum(qspec_then`SUC m`mp_tac)
      \\ simp[] )
    \\ first_x_assum(qspec_then`PRE j`mp_tac)
    \\ simp[]
    \\ metis_tac[arithmeticTheory.SUC_PRE] )
  \\ `r1 = MAP f r2`
  by (
    simp[Abbr`r1`, Abbr`r2`]
    \\ qmatch_goalsub_abbrev_tac`FILTER f2`
    \\ `f2 = (\i. !j. i <= j /\ (j < n) ==> f i <> f (SUC j)) o SUC`
    by (
      simp[Abbr`f2`, FUN_EQ_THM]
      \\ simp[arithmeticTheory.LESS_EQ] )
    \\ simp[GSYM MAP_MAP_o, GSYM rich_listTheory.FILTER_MAP]
    \\ simp[MAP_GENLIST]
    \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ simp[FUN_EQ_THM]
    \\ gen_tac
    \\ CONV_TAC(RAND_CONV(Ho_Rewrite.ONCE_REWRITE_CONV[arithmeticTheory.FORALL_NUM]))
    \\ simp[arithmeticTheory.LESS_EQ] )
  \\ rw[]
QED

Theorem nub_MAP_INJ:
  INJ f (set ls) UNIV ==>
  nub (MAP f ls) = MAP f (nub ls)
Proof
  Induct_on`ls`
  \\ rw[]
  \\ simp[nub_def]
  \\ simp[Once COND_RAND, SimpRHS]
  \\ `INJ f (set ls) UNIV`
  by (
    irule INJ_SUBSET
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[SUBSET_DEF] )
  \\ fs[]
  \\ simp[MEM_MAP]
  \\ fs[INJ_DEF]
  \\ metis_tac[]
QED

Theorem set_MAP_nub[simp]:
  set (MAP f (nub ls)) = set (MAP f ls)
Proof
  rw[EXTENSION, MEM_MAP]
QED
(* -- *)

Definition cf_matrix_def:
  cf_matrix c =
   MAP (λa. MAP (c.eval a) (QSORT (RC(SHORTLEX char_lt)) (SET_TO_LIST c.env)))
       (QSORT (RC(SHORTLEX char_lt)) (SET_TO_LIST c.agent))
End

Theorem RC_SHORTLEX_char_lt_transitive[simp]:
  transitive (RC (SHORTLEX char_lt))
Proof
  irule transitive_RC
  \\ irule SHORTLEX_transitive
  \\ simp[transitive_def, char_lt_def]
QED

Theorem RC_SHORTLEX_char_lt_total[simp]:
  total (RC (SHORTLEX char_lt))
Proof
  irule SHORTLEX_total
  \\ simp[total_def, RC_DEF, char_lt_def]
  \\ Cases \\ Cases \\ simp[]
QED

Theorem RC_SHORTLEX_char_lt_antisymmetric[simp]:
  antisymmetric (RC (SHORTLEX char_lt))
Proof
  simp[antisymmetric_def]
  \\ Induct \\ simp[]
  \\ gen_tac \\ Cases \\ simp[]
  \\ rw[] \\ fs[] \\ rfs[char_lt_def]
QED

Theorem QSORT_char_lt_SET_TO_LIST:
∀x.
  (FINITE ls ⇒
   QSORT (RC(SHORTLEX char_lt)) (x ++ SET_TO_LIST (s INSERT ls)) =
     QSORT (RC(SHORTLEX char_lt)) (x ++ if s ∈ ls then SET_TO_LIST ls else s::(SET_TO_LIST ls)))
Proof
  gen_tac \\ simp[]
  \\ strip_tac
  \\ DEP_REWRITE_TAC[SORTS_PERM_EQ]
  \\ conj_tac
  >- ( simp[] \\ match_mp_tac QSORT_SORTS \\ simp[])
  \\ simp[PERM_APPEND_IFF]
  \\ simp[PERM_SET_TO_LIST_INSERT]
QED

Theorem QSORT_char_lt_SET_TO_LIST_init =
  QSORT_char_lt_SET_TO_LIST |> Q.SPEC`[]` |> SIMP_RULE(srw_ss())[]

Definition permute_rows_def:
  permute_rows f m = GENLIST (λn. EL (f n) m) (LENGTH m)
End

Definition permute_cols_def:
  permute_cols f m = MAP (λr. GENLIST (λn. EL (f n) r) (LENGTH r)) m
End

Theorem permute_rows_I[simp]:
  permute_rows I m = m
Proof
  rw[permute_rows_def, LIST_EQ_REWRITE]
QED

Theorem permute_cols_I[simp]:
  permute_cols I m = m
Proof
  rw[permute_cols_def, LIST_EQ_REWRITE, EL_MAP]
QED

Theorem permute_rows_cols_comm:
  (∀i. (i < LENGTH m) ⇒ pr i < LENGTH m)
  ⇒
  permute_rows pr (permute_cols pc m) =
  permute_cols pc (permute_rows pr m)
Proof
  rw[permute_rows_def, permute_cols_def]
  \\ simp[LIST_EQ_REWRITE]
  \\ rw[EL_MAP]
QED

Theorem LENGTH_permute_rows[simp]:
  LENGTH (permute_rows pr m) = LENGTH m
Proof
  rw[permute_rows_def]
QED

Theorem LENGTH_permute_cols[simp]:
  LENGTH (permute_cols pc m) = LENGTH m
Proof
  rw[permute_cols_def]
QED

Theorem EL_permute_rows[simp]:
  n < LENGTH m ⇒
  EL n (permute_rows pr m) = EL (pr n) m
Proof
  rw[permute_rows_def]
QED

Definition transpose_def:
  transpose m =
  GENLIST (λi. MAP (EL i) m) (LENGTH (HD m))
End

Theorem set_MAP_LENGTH_cf_matrix[simp]:
  ¬NULL (cf_matrix c) ∧ FINITE c.env ⇒
  set (MAP LENGTH (cf_matrix c)) = {CARD c.env}
Proof
  rw[cf_matrix_def, LIST_TO_SET_MAP, GSYM IMAGE_COMPOSE, NULL_EQ]
  \\ rw[combinTheory.o_DEF]
  \\ rw[IMAGE_EQ_SING]
  \\ rw[SET_TO_LIST_CARD]
QED

Theorem SING_set_MAP_LENGTH_cf_matrix[simp]:
  ¬NULL (cf_matrix c) ⇒
  SING (set (MAP LENGTH (cf_matrix c)))
Proof
  rw[cf_matrix_def, LIST_TO_SET_MAP, GSYM IMAGE_COMPOSE, NULL_EQ]
  \\ rw[combinTheory.o_DEF, SING_DEF]
  \\ rw[IMAGE_EQ_SING]
  \\ qexists_tac`LENGTH (SET_TO_LIST c.env)` \\ rw[]
QED

Theorem transpose_idem[simp]:
  SING (set (MAP LENGTH m)) ∧ ¬ NULL (HD m) ⇒
  transpose (transpose m) = m
Proof
  rw[transpose_def, NULL_EQ]
  \\ Cases_on`HD m` \\ fs[HD_GENLIST]
  \\ simp[Once LIST_EQ_REWRITE]
  \\ rw[]
  \\ simp[MAP_GENLIST]
  \\ simp[Once LIST_EQ_REWRITE, EL_MAP]
  \\ fs[SING_DEF, EXTENSION, MEM_MAP]
  \\ `0 < LENGTH m` by simp[]
  \\ metis_tac[MEM_EL, EL, LENGTH]
QED

Theorem permute_cols_transpose:
  SING (set (MAP LENGTH m)) ∧ (∀i. i < LENGTH m ⇒ p i < LENGTH m) ⇒
  permute_cols p (transpose m) = transpose (permute_rows p m)
Proof
  rw[permute_cols_def, transpose_def, permute_rows_def]
  \\ simp[Once LIST_EQ_REWRITE]
  \\ conj_asm1_tac
  >- (
    Cases_on`LENGTH m` \\ fs[HD_GENLIST]
    \\ fs[SING_DEF, EXTENSION, MEM_MAP, PULL_EXISTS]
    \\ `0 < LENGTH m` by simp[]
    \\ metis_tac[MEM_EL, EL] )
  \\ pop_assum (assume_tac o SYM)
  \\ simp[EL_MAP]
  \\ simp[MAP_GENLIST]
  \\ simp[Once LIST_EQ_REWRITE]
  \\ simp[EL_MAP]
QED

Theorem distinct_rows_permute_set:
  ALL_DISTINCT m1 ∧ ALL_DISTINCT m2 ∧ LENGTH m1 = LENGTH m2 ⇒
  ((∃p. p PERMUTES count (LENGTH m1) ∧
        m1 = permute_rows p m2) ⇔
   (set m1 = set m2))
Proof
  rw[EQ_IMP_THM]
  >- (
    rw[EXTENSION]
    \\ rw[permute_rows_def, MEM_GENLIST]
    \\ rw[MEM_EL]
    \\ fs[BIJ_DEF, SURJ_DEF]
    \\ metis_tac[] )
  \\ rw[Once LIST_EQ_REWRITE]
  \\ fs[EXTENSION]
  \\ rfs[MEM_EL]
  \\ qexists_tac`λi. @j. (j < LENGTH m2) ∧ EL i m1 = EL j m2`
  \\ fs[EL_ALL_DISTINCT_EL_EQ]
  \\ simp[BIJ_DEF, INJ_DEF, SURJ_DEF]
  \\ metis_tac[]
QED

Theorem ALL_DISTINCT_permute_cols:
  set (MAP LENGTH m) = {l} ∧ pc PERMUTES (count l) ⇒
  (ALL_DISTINCT (permute_cols pc m) = ALL_DISTINCT m)
Proof
  rw[EL_ALL_DISTINCT_EL_EQ, permute_cols_def, EL_MAP]
  \\ `∀n. (n < LENGTH m) ⇒ LENGTH (EL n m) = l`
  by (
    fs[EXTENSION, MEM_MAP, PULL_EXISTS, MEM_EL]
    \\ metis_tac[] )
  \\ rw[Once LIST_EQ_REWRITE]
  \\ fs[BIJ_DEF, INJ_DEF, SURJ_DEF]
  \\ rw[Once LIST_EQ_REWRITE]
  \\ metis_tac[]
QED

Theorem LENGTH_transpose_nub:
  SING (set (MAP LENGTH m)) ⇒
  LENGTH (transpose (nub m)) = LENGTH (transpose m)
Proof
  rw[transpose_def]
  \\ qmatch_goalsub_abbrev_tac`LENGTH (HD ls)`
  \\ `EVERY (λl. LENGTH l = LENGTH (HD m)) ls`
  by (
    rw[Abbr`ls`, EVERY_MEM, MEM_GENLIST, PULL_EXISTS]
    \\ fs[SING_DEF, EXTENSION, MEM_MAP, MEM_EL]
    \\ `0 < LENGTH m` by simp[]
    \\ metis_tac[EL])
  \\ Cases_on`ls` \\ fs[]
QED

Theorem set_MAP_LENGTH_transpose:
  ¬ NULL (HD m) ⇒
  set (MAP LENGTH (transpose m)) = { LENGTH m }
Proof
  rw[transpose_def, MAP_GENLIST, combinTheory.o_DEF]
  \\ simp[GSYM (SIMP_RULE std_ss [combinTheory.K_DEF]
                rich_listTheory.REPLICATE_GENLIST)]
  \\ simp[EXTENSION]
  \\ Cases_on`HD m` \\ fs[]
QED

Theorem LENGTH_transpose_nub_transpose:
  SING (set (MAP LENGTH m)) ∧ ¬NULL(HD m) ⇒
  LENGTH (transpose (nub (transpose m))) = LENGTH m
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[LENGTH_transpose_nub]
  \\ DEP_REWRITE_TAC[transpose_idem]
  \\ DEP_REWRITE_TAC[set_MAP_LENGTH_transpose]
  \\ simp[]
QED

Theorem ALL_DISTINCT_transpose_nub_transpose:
  SING (set (MAP LENGTH m)) ∧ ¬ NULL (HD m) ⇒
  (ALL_DISTINCT (transpose (nub (transpose m))) ⇔
   ALL_DISTINCT m)
Proof
  strip_tac
  \\ imp_res_tac LENGTH_transpose_nub_transpose
  \\ fs[transpose_def]
  \\ rw[ALL_DISTINCT_GENLIST]
  \\ simp[MAP_EQ_f]
  \\ simp[MEM_GENLIST, PULL_EXISTS]
  \\ `EVERY (λl. LENGTH l = LENGTH (HD m)) m`
  by (
    fs[EVERY_MEM, SING_DEF, EXTENSION, MEM_MAP, PULL_EXISTS]
    \\ Cases_on`m` \\ fs[]
    \\ metis_tac[] )
  \\ simp[EL_MAP, GSYM AND_IMP_INTRO]
  \\ simp[EL_ALL_DISTINCT_EL_EQ]
  \\ simp[Once LIST_EQ_REWRITE]
  \\ fs[EVERY_MEM, MEM_EL]
  \\ metis_tac[]
QED

Theorem EL_transpose_nub_eq:
  SING (set (MAP LENGTH m)) ∧
  (n1 < LENGTH (transpose m)) ∧ (n2 < LENGTH (transpose m)) ⇒
  (EL n1 (transpose (nub m)) = EL n2 (transpose (nub m)) ⇔
   EL n1 (transpose m) = EL n2 (transpose m))
Proof
  rw[]
  \\ imp_res_tac LENGTH_transpose_nub
  \\ fs[transpose_def, EL_GENLIST]
  \\ simp[MAP_EQ_f]
QED

Theorem LENGTH_nub_transpose_nub:
  SING (set (MAP LENGTH m)) ⇒
  LENGTH (nub (transpose (nub m))) = LENGTH (nub (transpose m))
Proof
  rw[GSYM CARD_LIST_TO_SET_EQN]
  \\ irule FINITE_BIJ_CARD
  \\ simp[]
  \\ imp_res_tac LENGTH_transpose_nub
  \\ qexists_tac`λc. EL (LEAST i. (i < LENGTH (transpose m)) ∧
                                  (c = EL i (transpose (nub m)))) (transpose m)`
  \\ simp[BIJ_DEF, INJ_DEF, GSYM CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    rw[MEM_EL]
    \\ numLib.LEAST_ELIM_TAC
    \\ metis_tac[] )
  \\ conj_tac
  >- (
    simp[MEM_EL]
    \\ rpt gen_tac \\ strip_tac
    \\ numLib.LEAST_ELIM_TAC
    \\ numLib.LEAST_ELIM_TAC
    \\ rw[]
    >- metis_tac[]
    >- metis_tac[]
    \\ DEP_REWRITE_TAC[EL_transpose_nub_eq]
    \\ simp[] )
  \\ rw[SURJ_DEF]
  \\ pop_assum mp_tac
  \\ rw[MEM_EL, PULL_EXISTS]
  \\ qexists_tac`n` \\ rw[]
  \\ numLib.LEAST_ELIM_TAC
  \\ metis_tac[EL_transpose_nub_eq]
QED

Theorem set_permute_rows:
  p PERMUTES count (LENGTH m) ⇒
  set (permute_rows p m) = set m
Proof
  rw[EXTENSION, permute_rows_def, MEM_GENLIST]
  \\ rw[MEM_EL]
  \\ fs[BIJ_IFF_INV]
  \\ metis_tac[]
QED

Theorem permute_cols_nub:
  set (MAP LENGTH m) = {l} ∧ p PERMUTES count l ⇒
  permute_cols p (nub m) = nub (permute_cols p m)
Proof
  rw[permute_cols_def]
  \\ DEP_REWRITE_TAC[nub_MAP_INJ]
  \\ rw[INJ_DEF]
  \\ fs[LIST_TO_SET_MAP, EXTENSION]
  \\ gs[LIST_EQ_REWRITE]
  \\ fs[BIJ_IFF_INV]
  \\ metis_tac[]
QED

Theorem permute_rows_compose:
  (∀x. (x < LENGTH ls) ⇒ p1 x < LENGTH ls) ⇒
  permute_rows p1 (permute_rows p2 ls) = permute_rows (p2 o p1) ls
Proof
 rw[permute_rows_def, LIST_EQ_REWRITE, EL_GENLIST]
QED

Theorem eq_rows_transpose_swap:
  set (MAP LENGTH m1) = {LENGTH m2} ∧
  set (MAP LENGTH m2) = {LENGTH m1} ∧
  ¬NULL (HD m1) ∧ ¬NULL (HD m2) ∧
  ALL_DISTINCT m1 ∧ ALL_DISTINCT m2 ∧
  ALL_DISTINCT (transpose m1) ∧ ALL_DISTINCT (transpose m2)
  ⇒ (
  (∃p. p PERMUTES count (LENGTH m2) ∧
       set m1 = set (transpose (permute_rows p m2))) ⇔
  (∃p. p PERMUTES count (LENGTH m1) ∧
       set (transpose m1) = set (permute_cols p m2)) )
Proof
  qho_match_abbrev_tac`P m1 m2 ⇒ (Q m1 m2 ⇔ R m1 m2)`
  \\ `∀m1 m2. P m1 m2 ∧ Q m1 m2 ⇒ R m1 m2`
  suffices_by (
    rw[]
    \\ EQ_TAC >- metis_tac[]
    \\ `LENGTH (transpose m1) = LENGTH m2 ∧
        LENGTH (transpose m2) = LENGTH m1`
    by (
      rw[transpose_def, Abbr`P`]
      \\ Cases_on`m1` \\ gs[EXTENSION]
      \\ Cases_on`m2` \\ gs[EXTENSION]
      \\ metis_tac[] )
    \\ `P (transpose m1) (transpose m2)`
    by (
      fs[Abbr`P`, SING_DEF]
      \\ DEP_REWRITE_TAC[set_MAP_LENGTH_transpose]
      \\ simp[]
      \\ simp[transpose_def]
      \\ Cases_on`HD m1` \\ fs[]
      \\ Cases_on`HD m2` \\ fs[]
      \\ simp[GENLIST_CONS, NULL_EQ]
      \\ CCONTR_TAC \\ gs[] )
    \\ strip_tac
    \\ `Q (transpose m1) (transpose m2)`
    by (
      gs[Abbr`Q`, Abbr`R`, Abbr`P`]
      \\ qexists_tac`p`
      \\ conj_tac >- gs[]
      \\ DEP_REWRITE_TAC[GSYM permute_cols_transpose]
      \\ DEP_REWRITE_TAC[set_MAP_LENGTH_transpose]
      \\ gs[]
      \\ fs[BIJ_DEF, SURJ_DEF] )
    \\ first_x_assum drule
    \\ simp[Abbr`R`]
    \\ DEP_REWRITE_TAC[transpose_idem]
    \\ conj_tac >- gs[Abbr`P`]
    \\ strip_tac
    \\ simp[Abbr`Q`]
    \\ qexists_tac`p`
    \\ DEP_REWRITE_TAC[permute_cols_transpose]
    \\ gs[Abbr`P`]
    \\ fs[BIJ_DEF, SURJ_DEF] )
  \\ rw[Abbr`P`, Abbr`Q`, Abbr`R`]
  \\ `PERM m1 (transpose (permute_rows p m2))` by (
    irule PERM_ALL_DISTINCT
    \\ rw[]
    \\ DEP_REWRITE_TAC[GSYM permute_cols_transpose]
    \\ DEP_REWRITE_TAC[Q.GEN`l`ALL_DISTINCT_permute_cols]
    \\ simp[]
    \\ DEP_REWRITE_TAC[set_MAP_LENGTH_transpose]
    \\ simp[]
    \\ fs[BIJ_DEF, SURJ_DEF] )
  \\ fs[PERM_BIJ_IFF]
  \\ fs[GSYM permute_rows_def]
  \\ `∃p. p PERMUTES count (LENGTH m1) ∧
          PERM (transpose m1) (permute_cols p m2)`
     suffices_by metis_tac[PERM_LIST_TO_SET]
  \\ simp[PERM_BIJ_IFF, PULL_EXISTS, GSYM permute_rows_def]
  \\ simp[Once transpose_def]
  \\ simp[Once transpose_def]
  \\ `LENGTH (HD m1) = LENGTH m2`
  by ( Cases_on`m1` \\ fs[EXTENSION] \\ metis_tac[] )
  \\ simp[]
  \\ imp_res_tac BIJ_LINV_BIJ
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qmatch_goalsub_abbrev_tac`permute_cols g'`
  \\ qmatch_goalsub_abbrev_tac`permute_rows g`
  \\ qpat_x_assum`_ = permute_rows _ _`mp_tac
  \\ simp[transpose_def, permute_rows_def, permute_cols_def]
  \\ simp[Once LIST_EQ_REWRITE, GSYM AND_IMP_INTRO]
  \\ strip_tac
  \\ simp[MAP_GENLIST]
  \\ disch_then(assume_tac o GSYM)
  \\ simp[Once LIST_EQ_REWRITE]
  \\ simp[EL_MAP]
  \\ rpt strip_tac
  \\ `g x < LENGTH m2` by fs[BIJ_DEF, SURJ_DEF]
  \\ simp[]
  \\ simp[Once LIST_EQ_REWRITE]
  \\ conj_asm1_tac
  >- ( rfs[EXTENSION,LIST_TO_SET_MAP,MEM_EL] \\ metis_tac[EL_MAP] )
  \\ simp[EL_MAP]
  \\ rpt strip_tac
  \\ first_assum(qspec_then`g' x'`mp_tac)
  \\ impl_tac >- fs[BIJ_DEF, SURJ_DEF]
  \\ `p' (g' x') = x'` by metis_tac[BIJ_LINV_INV, IN_COUNT]
  \\ simp[]
  \\ metis_tac[BIJ_LINV_INV, IN_COUNT]
QED

val _ = export_theory();
