(*
Copyright 2021 DeepMind Technologies Limited.

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

open HolKernel bossLib boolLib Parse dep_rewrite
     bagTheory containerTheory primeFactorTheory dividesTheory
     arithmeticTheory prim_recTheory helperNumTheory bagTheory listTheory helperListTheory sortingTheory
     pairTheory pred_setTheory helperSetTheory partitionTheory

val _ = new_theory"factoredSet";

Theorem BAG_GEN_PROD_LIST_TO_BAG: (* note: PROD is defined in helperList *)
  !l n. BAG_GEN_PROD (LIST_TO_BAG l) n = n * PROD l
Proof
  Induct
  >- rw[BAG_GEN_PROD_def]
  \\ rw[BAG_GEN_PROD_REC]
QED

(* Factorizations *)

Definition BIGPROD_def:
  BIGPROD sos = { f | (!s. if s IN sos then (?x. f s = (s, x) /\ x IN s)
                           else f s = ARB) }
End

Theorem BINARY_BIGPROD:
  a <> b ==>
  BIJ (\f. (SND(f a), SND(f b))) (BIGPROD {a; b}) (a CROSS b)
Proof
  rw[BIJ_IFF_INV, BIGPROD_def]
  \\ TRY(first_x_assum(qspec_then`a`mp_tac)\\simp[]\\strip_tac\\simp[]\\NO_TAC)
  \\ TRY(first_x_assum(qspec_then`b`mp_tac)\\simp[]\\strip_tac\\simp[]\\NO_TAC)
  \\ qexists_tac`\x s. if s = a then (a, FST x) else
                       if s = b then (b, SND x) else ARB`
  \\ rw[]
  \\ rw[Once FUN_EQ_THM]
  \\ rw[]
  \\ first_assum(qspec_then`a`mp_tac)
  \\ first_assum(qspec_then`b`mp_tac)
  \\ first_x_assum(qspec_then`s`mp_tac)
  \\ rw[] \\ rw[]
QED

Theorem BIGPROD_eq_empty[simp]:
  BIGPROD sos = {} <=> {} IN sos
Proof
  rw[BIGPROD_def]
  \\ rw[Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  >- (
    CCONTR_TAC
    \\ last_x_assum mp_tac
    \\ simp[]
    \\ qexists_tac`\s. if s IN sos then (s, CHOICE s) else ARB`
    \\ rw[]
    \\ metis_tac[CHOICE_DEF])
  \\ qexists_tac`{}` \\ rw[]
QED

Theorem BIGPROD_empty[simp]:
  BIGPROD {} = {K ARB}
Proof
  rw[BIGPROD_def]
  \\ simp[Once EXTENSION]
  \\ simp[FUN_EQ_THM]
QED

Theorem BIGPROD_INSERT:
  s NOTIN sos ==>
  BIGPROD (s INSERT sos) =
  BIGUNION (IMAGE (\f. IMAGE (\x t. if t = s then (s, x) else f t) s)
                  (BIGPROD sos))
Proof
  rw[Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
  >- (
    fs[BIGPROD_def]
    \\ simp[Once FUN_EQ_THM]
    \\ qexists_tac`(s =+ ARB) x`
    \\ qexists_tac`SND (x s)`
    \\ conj_tac
    >- (
      rw[combinTheory.APPLY_UPDATE_THM]
      \\ first_x_assum(qspec_then`s`mp_tac)
      \\ rw[] \\ rw[] )
    \\ qx_gen_tac`t`
    \\ rw[combinTheory.APPLY_UPDATE_THM] \\ fs[]
    \\ first_x_assum(qspec_then`t`mp_tac)
    \\ rw[] )
  \\ fs[BIGPROD_def]
  \\ qx_gen_tac`t`
  \\ rw[] \\ fs[]
  \\ metis_tac[]
QED

Theorem FINITE_BIGPROD:
  FINITE sos /\ EVERY_FINITE sos ==> FINITE (BIGPROD sos)
Proof
  simp[GSYM AND_IMP_INTRO]
  \\ qid_spec_tac`sos`
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[] \\ fs[]
  \\ rw[BIGPROD_INSERT]
  \\ irule IMAGE_FINITE
  \\ rw[]
QED

Theorem CARD_BIGPROD:
  FINITE sos /\ EVERY_FINITE sos ==>
  CARD (BIGPROD sos) = PROD_IMAGE CARD sos
Proof
  simp[GSYM AND_IMP_INTRO]
  \\ qid_spec_tac`sos`
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ simp[]
  \\ conj_tac
  >- simp[PROD_IMAGE_THM]
  \\ rpt strip_tac \\ fs[]
  \\ simp[PROD_IMAGE_THM]
  \\ `sos DELETE e = sos` by metis_tac[DELETE_NON_ELEMENT]
  \\ pop_assum SUBST1_TAC
  \\ first_x_assum(SUBST1_TAC o SYM)
  \\ simp[BIGPROD_INSERT]
  \\ qmatch_goalsub_abbrev_tac`BIGUNION s`
  \\ `PAIR_DISJOINT s`
  by (
    qx_genl_tac[`a`,`b`]
    \\ strip_tac
    \\ simp[IN_DISJOINT]
    \\ CCONTR_TAC \\ fs[]
    \\ fs[Abbr`s`]
    \\ rw[] \\ fs[] \\ rw[]
    \\ qpat_x_assum`_ = _`mp_tac
    \\ simp[Once FUN_EQ_THM]
    \\ Cases_on`f = f'` \\ fs[]
    \\ pop_assum mp_tac
    \\ simp[Once FUN_EQ_THM, PULL_EXISTS]
    \\ qx_gen_tac`x`
    \\ strip_tac
    \\ fs[BIGPROD_def]
    \\ `x IN sos` by metis_tac[]
    \\ qexists_tac`x`
    \\ rw[] \\ fs[] )
  \\ `FINITE s`
  by (
    simp[Abbr`s`]
    \\ irule IMAGE_FINITE
    \\ irule FINITE_BIGPROD
    \\ simp[])
  \\ drule CARD_BIGUNION_SAME_SIZED_SETS
  \\ Cases_on`e = {}`
  >- (
    simp[]
    \\ disch_then kall_tac
    \\ gs[Abbr`s`]
    \\ DEP_REWRITE_TAC[CARD_EQ_0]
    \\ simp[IMAGE_EQ_SING, PULL_EXISTS] )
  \\ disch_then(qspec_then`CARD e`mp_tac)
  \\ `!x. x IN s ==> FINITE x /\ CARD x = CARD e`
  by (
    rw[Abbr`s`, PULL_EXISTS]
    \\ irule INJ_CARD_IMAGE_EQ
    \\ simp[INJ_DEF]
    \\ qexists_tac`UNIV`
    \\ rw[]
    \\ pop_assum mp_tac
    \\ simp[Once FUN_EQ_THM]
    \\ disch_then(qspec_then`e`mp_tac)
    \\ simp[])
  \\ rw[]
  \\ simp[Abbr`s`]
  \\ irule INJ_CARD_IMAGE_EQ
  \\ simp[FINITE_BIGPROD]
  \\ simp[INJ_DEF]
  \\ qexists_tac`UNIV`
  \\ rw[]
  \\ simp[FUN_EQ_THM]
  \\ fs[BIGPROD_def]
  \\ rw[]
  \\ reverse(Cases_on`x IN sos`) >- metis_tac[]
  \\ qpat_x_assum`_ = _`mp_tac
  \\ simp[Once EXTENSION]
  \\ dsimp[EQ_IMP_THM] \\ rw[Once FUN_EQ_THM]
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Definition factorises_def:
  factorises b w <=>
    (!v. v IN b ==> v partitions w /\ v <> {w}) /\
    BIJ (\x v. if v IN b then (v, part v x) else ARB) w (BIGPROD b)
End

val _ = set_fixity "factorises" (Infix(NONASSOC, 425))

Theorem factorises_distinguish:
  b factorises w /\ s1 IN w /\ s2 IN w ==>
  (s1 = s2 <=> !v. v IN b ==> part v s1 = part v s2)
Proof
  rw[factorises_def]
  \\ eq_tac >- rw[]
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`BIJ p`
  \\ `p s1 = p s2` suffices_by metis_tac[BIJ_DEF, INJ_DEF]
  \\ simp[Abbr`p`]
QED

Theorem factorises_alt:
  b factorises w <=>
    (!v. v IN b ==> v partitions w /\ v <> {w}) /\
    (!f. (!v. v IN b ==> f v IN w) ==>
      (?!x. x IN w /\ !v. v IN b ==> part v x = part v (f v)))
Proof
  rw[factorises_def]
  \\ qmatch_abbrev_tac`A /\ B <=> _`
  \\ Cases_on`A = F` \\ fs[]
  \\ fs[Abbr`A`, Abbr`B`]
  \\ qmatch_goalsub_abbrev_tac`BIJ p`
  \\ eq_tac \\ strip_tac
  >- (
    gen_tac \\ strip_tac
    \\ simp[EXISTS_UNIQUE_THM]
    \\ reverse conj_tac
    >- (
      rw[]
      \\ `b factorises w` by rw[factorises_def]
      \\ metis_tac[factorises_distinguish])
    \\ qexists_tac`LINV p w (\v. if v IN b then (v, part v (f v)) else ARB)`
    \\ qmatch_goalsub_abbrev_tac`LINV p w q`
    \\ `q IN BIGPROD b`
    by (
      simp[BIGPROD_def, Abbr`q`, Abbr`p`]
      \\ metis_tac[part_in_partition])
    \\ conj_asm1_tac >- metis_tac[BIJ_LINV_BIJ, BIJ_DEF, INJ_DEF]
    \\ rw[]
    \\ `q v = p (LINV p w q) v` by metis_tac[BIJ_LINV_THM]
    \\ qmatch_goalsub_abbrev_tac`part v z`
    \\ `(v, part v z) = (v, part v (f v))` by metis_tac[]
    \\ fs[])
  \\ simp[BIJ_DEF]
  \\ `!x. x IN w ==> p x IN (BIGPROD b)`
  by ( simp[Abbr`p`, BIGPROD_def] \\ metis_tac[part_in_partition] )
  \\ simp[INJ_DEF]
  \\ conj_tac
  >- (
    rw[Abbr`p`]
    \\ first_x_assum(qspec_then`K x`mp_tac)
    \\ simp[EXISTS_UNIQUE_THM]
    \\ strip_tac
    \\ qpat_x_assum`(\v. _) = _`mp_tac
    \\ simp[FUN_EQ_THM] \\ strip_tac
    \\ first_x_assum irule
    \\ simp[]
    \\ rpt strip_tac
    \\ first_x_assum(qspec_then`v`mp_tac)
    \\ simp[])
  \\ simp[SURJ_DEF]
  \\ qx_gen_tac`f` \\ strip_tac
  \\ `!v. v IN b ==> SND (f v) SUBSET w /\ SND (f v) <> {}`
  by (
    fs[BIGPROD_def]
    \\ gen_tac \\ strip_tac
    \\ first_x_assum (qspec_then`v`mp_tac)
    \\ simp[] \\ strip_tac
    \\ simp[]
    \\ metis_tac[partitions_thm])
  \\ `?g. !v. v IN b ==> g v IN SND (f v)`
  by (
    simp[GSYM SKOLEM_THM]
    \\ gen_tac \\ Cases_on`v IN b` \\ simp[]
    \\ metis_tac[MEMBER_NOT_EMPTY])
  \\ `!x. x IN b ==> g x IN w` by metis_tac[SUBSET_DEF]
  \\ `?s. s IN w /\ !v. v IN b ==> part v s = part v (g v)`
  by metis_tac[EXISTS_UNIQUE_THM]
  \\ qexists_tac`s` \\ simp[]
  \\ simp[Abbr`p`]
  \\ simp[FUN_EQ_THM]
  \\ gen_tac
  \\ reverse IF_CASES_TAC
  >- ( fs[BIGPROD_def] \\ metis_tac[] )
  \\ fs[BIGPROD_def]
  \\ `?x. f v = (v, x) /\ x IN v` by metis_tac[] \\ simp[]
  \\ `g v IN x` by metis_tac[SND]
  \\ irule EQ_SYM
  \\ irule part_unique
  \\ simp[]
  \\ metis_tac[]
QED

Theorem factorises_unique_inter:
  b factorises w <=>
    (!v. v IN b ==> v partitions w /\ v <> {w}) /\
    (!f. (!v. v IN b ==> f v IN v) ==>
         (?!x. x IN w /\ x IN BIGINTER (IMAGE f b)))
Proof
  rw[factorises_alt]
  \\ qmatch_goalsub_abbrev_tac`A ∧ _`
  \\ Cases_on`A = T` \\ fs[] \\ fs[Abbr`A`]
  \\ Cases_on`b = {}` \\ gs[]
  \\ eq_tac \\ rpt strip_tac \\ gs[PULL_EXISTS]
  >- (
    `b factorises w` by simp[factorises_alt]
    \\ first_x_assum(qspec_then`CHOICE o f`mp_tac)
    \\ impl_tac
    >- (
      rw[]
      \\ `v partitions w` by metis_tac[]
      \\ `f v ∈ v` by metis_tac[]
      \\ `f v ≠ ∅` by metis_tac[partitions_thm]
      \\ `CHOICE (f v) ∈ f v` by metis_tac[CHOICE_DEF]
      \\ metis_tac[partitions_thm, SUBSET_DEF])
    \\ simp[EXISTS_UNIQUE_ALT]
    \\ disch_then(qx_choose_then`x`strip_assume_tac)
    \\ qexists_tac`x`
    \\ `∀v. v ∈ b ⇒ part v x = part v (CHOICE (f v))` by metis_tac[]
    \\ `∀v. v ∈ b ⇒ f v ≠ ∅ ∧ f v ⊆ w` by metis_tac[partitions_thm]
    \\ `∀v. v ∈ b ⇒ part v (CHOICE (f v)) = f v`
    by (
      rpt strip_tac
      \\ irule EQ_SYM
      \\ irule part_unique
      \\ metis_tac[CHOICE_DEF, SUBSET_DEF])
    \\ `∀v. v ∈ b ⇒ x ∈ part v (CHOICE (f v))` by metis_tac[in_part]
    \\ reverse(rw[EQ_IMP_THM])
    >- metis_tac[]
    >- metis_tac[SUBSET_DEF]
    \\ fsrw_tac[DNF_ss][EQ_IMP_THM]
    \\ first_x_assum irule \\ simp[]
    \\ metis_tac[part_unique])
  \\ first_x_assum(qspec_then`λv. part v (f v)`mp_tac)
  \\ impl_tac
  >- (
    rw[]
    \\ irule part_in_partition
    \\ metis_tac[])
  \\ rw[EXISTS_UNIQUE_ALT]
  \\ qexists_tac`x`
  \\ rw[]
  \\ reverse(Cases_on`x' ∈ w`) >- metis_tac[] \\ simp[]
  \\ first_x_assum(qspec_then`x'`(SUBST1_TAC o SYM)) \\ simp[]
  \\ rw[EQ_IMP_THM]
  >- metis_tac[in_part]
  \\ irule EQ_SYM
  \\ irule part_unique
  \\ metis_tac[part_in_partition]
QED

Theorem factors_DISJOINT:
  b factorises w /\ v1 IN b /\ v2 IN b /\ v1 <> v2 ==> DISJOINT v1 v2
Proof
  simp[IN_DISJOINT]
  \\ strip_tac
  \\ qx_gen_tac`s`
  \\ CCONTR_TAC \\ fs[]
  \\ fs[factorises_alt]
  \\ `?t. t IN v1 /\ t <> s`
  by (
    CCONTR_TAC \\ fs[]
    \\ `v1 = {s}` by (simp[Once EXTENSION] \\ metis_tac[])
    \\ metis_tac[SING_partitions])
  \\ `DISJOINT s t` by metis_tac[partitions_DISJOINT]
  \\ `?x. x IN s /\ x IN w`
  by metis_tac[partitions_thm, MEMBER_NOT_EMPTY, SUBSET_DEF]
  \\ `?y. y IN t /\ y IN w`
  by metis_tac[partitions_thm, MEMBER_NOT_EMPTY, SUBSET_DEF]
  \\ `s = part v1 x /\ t = part v1 y /\ s = part v2 x` by metis_tac[part_unique]
  \\ `x <> y` by metis_tac[]
  \\ first_x_assum(qspec_then`\v. if v = v1 then x else y`mp_tac)
  \\ impl_tac >- rw[]
  \\ simp[EXISTS_UNIQUE_THM]
  \\ metis_tac[in_part, part_unique, IN_DISJOINT]
QED

Theorem factorises_common_refinement_discrete:
  b factorises w ==>
  common_refinement w b = discrete_partition w
Proof
  strip_tac
  \\ rw[common_refinement_def]
  \\ rw[discrete_partition_def]
  \\ rw[partition_def]
  \\ `!x. x IN w ==> {y | y IN w /\ !v. v IN b ==> part v x = part v y} = {x}`
  by (
    rw[Once EXTENSION]
    \\ rw[EQ_IMP_THM]
    \\ metis_tac[factorises_distinguish])
  \\ rw[Once EXTENSION]
  \\ metis_tac[]
QED

(* not super useful? could also note that discrete_partition is always distinguishing *)
Theorem distinguish_insufficient_for_factorise:
  w = count 3 ∧
  v1 = {{0;1};{2}} ∧
  v2 = {{0};{1;2}} ∧
  b = {v1;v2}
  ⇒
  (!v. v IN b ==> v partitions w /\ v <> {w}) ∧ (w = {} ==> b = {{}}) ∧
  (!x y. x IN w /\ y IN w ==> (x = y <=> !v. v IN b ==> part v x = part v y))
  ∧ ¬(b factorises w)
Proof
  strip_tac
  \\ conj_asm1_tac
  >- (
    rw[partitions_thm, EXISTS_UNIQUE_THM] \\ gs[SUBSET_DEF]
    \\ dsimp[] \\ EVAL_TAC )
  \\ conj_tac >- (rw[] \\ fs[])
  \\ reverse conj_tac
  >- (
    rw[]
    \\ qmatch_goalsub_abbrev_tac`b factorises w`
    \\ dsimp[factorises_unique_inter]
    \\ qmatch_asmsub_abbrev_tac`b = {v1;v2}`
    \\ qexists_tac`λv. if v = v2 then {0} else {2}`
    \\ conj_tac >- ( rw[Abbr`b`] \\ rw[Abbr`v`] )
    \\ simp[EXISTS_UNIQUE_THM]
    \\ disj1_tac
    \\ CCONTR_TAC \\ fs[]
    \\ pop_assum mp_tac \\ simp[]
    \\ Cases_on`x = 0`
    >- (
      qexists_tac`v1`
      \\ simp[Abbr`b`]
      \\ rw[Abbr`v1`,Abbr`v2`]
      \\ pop_assum mp_tac \\ EVAL_TAC )
    \\ qexists_tac`v2`
    \\ rw[Abbr`b`] )
  \\ rw[]
  \\ Cases_on`x = y` \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`_ ∈ {v1;v2}`
  \\ dsimp[]
  \\ rpt strip_tac \\ fs[]
  \\ `part v1 0 = {0; 1} ∧
      part v1 1 = {0; 1} ∧
      part v1 2 = {2} ∧
      part v2 0 = {0} ∧
      part v2 1 = {1; 2} ∧
      part v2 2 = {1; 2}`
  by (
    rpt conj_tac
    \\ qmatch_goalsub_abbrev_tac`part vv q = p`
    \\ `q ∈ count 3` by simp[Abbr`q`]
    \\ `part vv q ∈ vv` by metis_tac[part_in_partition]
    \\ `q ∈ part vv q` by metis_tac[in_part]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[Abbr`vv`]
    \\ dsimp[Abbr`v1`, Abbr`v2`, Abbr`q`] )
  \\ `x ∈ count 3 ∧ y ∈ count 3` by simp[]
  \\ `x ∈ part v1 x ∧ y ∈ part v1 y ∧ x ∈ part v2 x ∧ y ∈ part v2 y`
  by metis_tac[in_part]
  \\ Cases_on`x = 0` \\ gs[]
  \\ Cases_on`x = 1` \\ gs[]
  \\ `x = 2` by simp[]
  \\ Cases_on`y = 0` >- gs[]
  \\ `y <> 2` by gs[]
  \\ `y = 1` by gs[]
  \\ fs[] \\ rfs[]
QED

Theorem discrete_partition_eq_empty:
  discrete_partition w = {} <=> w = {}
Proof
  rw[discrete_partition_def, Once EXTENSION]
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Definition chimera_def:
  chimera w b f = @x. x IN w /\ !v. v IN b ==> part v x = part v (f v)
End

Theorem chimera_thm:
  b factorises w ∧ (∀v. v ∈ b ⇒ f v ∈ w)⇒
  chimera w b f ∈ w ∧
  ∀v. v ∈ b ⇒ part v (chimera w b f) = part v (f v)
Proof
  strip_tac
  \\ simp[chimera_def]
  \\ SELECT_ELIM_TAC \\ simp[]
  \\ metis_tac[factorises_alt]
QED

Overload "chim" = ``\w b c s t. chimera w b (\x. if x IN c then s else t)``

Theorem chim_thm:
  b factorises w ∧ s ∈ w ∧ t ∈ w ⇒
  chim w b c s t ∈ w ∧
  ∀v. v ∈ b ⇒ part v (chim w b c s t) =  part v (if v ∈ c then s else t)
Proof
  strip_tac
  \\ drule chimera_thm
  \\ qmatch_goalsub_abbrev_tac`part _ (chimera _ _ f)`
  \\ disch_then(qspec_then`f`mp_tac)
  \\ impl_tac >- rw[Abbr`f`]
  \\ rw[]
QED

Theorem chim_same:
  b factorises w ∧ c ⊆ b ∧ s ∈ w ⇒
  chim w b c s s = s
Proof
  rw[chimera_def]
  \\ SELECT_ELIM_TAC
  \\ rw[] >- metis_tac[]
  \\ metis_tac[factorises_distinguish]
QED

Theorem chim_DIFF:
  b factorises w ∧ c ⊆ b ∧ s ∈ w ∧ t ∈ w ⇒
  chim w b (b DIFF c) s t = chim w b c t s
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm]
  \\ rw[] \\ fs[]
QED

Theorem chim_UNION:
  b factorises w ∧ c ⊆ b ∧ d ⊆ b ∧ s ∈ w ∧ t ∈ w ⇒
  chim w b (c ∪ d) s t = chim w b c s (chim w b d s t)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm]
  \\ rw[] \\ gs[]
  \\ simp[chim_thm]
QED

Theorem chim_INTER:
  b factorises w ∧ c ⊆ b ∧ d ⊆ b ∧ s ∈ w ∧ t ∈ w ⇒
  chim w b (c ∩ d) s t = chim w b c (chim w b d s t) t
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm]
  \\ rw[] \\ gs[]
  \\ simp[chim_thm]
QED

Theorem chim_squeeze:
  b factorises w ∧ s ∈ w ∧ t ∈ w ∧ r ∈ w ⇒
  chim w b c s (chim w b c t r) = chim w b c s r ∧
  chim w b c (chim w b c s t) r = chim w b c s r
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm]
  \\ conj_tac
  >- ( rw[] \\ simp[chim_thm] )
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm]
  \\ rw[] \\ simp[chim_thm]
QED

Theorem chim_compose:
  b factorises w ∧ s ∈ w ∧ t ∈ w ∧ r ∈ w ⇒
  chim w b c s (chim w b d t r) =
    chim w b d (chim w b c s t) (chim w b c s r) ∧
  chim w b c (chim w b d s t) r =
    chim w b d (chim w b c s r) (chim w b c t r)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm]
  \\ conj_tac >- ( rw[] \\ simp[chim_thm] )
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ simp[chim_thm] \\ rw[] \\ simp[chim_thm]
QED

Theorem chim_full[simp]:
  b factorises w ∧ s ∈ w ∧ t ∈ w ⇒
  chim w b b s t = s
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ rw[chim_thm]
QED

Theorem chim_empty:
  b factorises w ∧ s ∈ w ∧ t ∈ w ⇒
  chim w b ∅ s t = t
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ rw[chim_thm]
QED

Theorem chim_facts:
  b factorises w ∧ c ⊆ b ∧ d ⊆ b ∧ s ∈ w ∧ t ∈ w ∧ r ∈ w ⇒
  (∀v. v ∈ c ⇒ part v (chim w b c s t) = part v s) ∧
  (∀v. v ∈ b DIFF c ⇒ part v (chim w b c s t ) = part v t) ∧
  chim w b c s s = s ∧
  chim w b (b DIFF c) s t = chim w b c t s ∧
  chim w b (c ∪ d) s t = chim w b c s (chim w b d s t) ∧
  chim w b (c ∩ d) s t = chim w b c (chim w b d s t) t ∧
  chim w b c s (chim w b c t r) = chim w b c s r ∧
  chim w b c (chim w b c s t) r = chim w b c s r ∧
  chim w b c s (chim w b d t r) =
    chim w b d (chim w b c s t) (chim w b c s r) ∧
  chim w b c (chim w b d s t) r =
    chim w b d (chim w b c s r) (chim w b c t r) ∧
  chim w b b s t = s ∧
  chim w b ∅ s t = t
Proof
  strip_tac
  \\ conj_tac >- fs[SUBSET_DEF, chim_thm]
  \\ conj_tac >- fs[SUBSET_DEF, chim_thm]
  \\ conj_tac >- fs[chim_same]
  \\ conj_tac >- fs[chim_DIFF]
  \\ conj_tac >- fs[chim_UNION]
  \\ conj_tac >- fs[chim_INTER]
  \\ conj_tac >- fs[chim_squeeze]
  \\ conj_tac >- fs[chim_squeeze]
  \\ conj_tac >- fs[chim_compose]
  \\ conj_tac >- fs[chim_compose]
  \\ rw[chim_empty]
QED

Theorem chim_closed_INTER:
  b factorises w /\ c SUBSET b /\ d SUBSET b /\ e SUBSET w /\
  { chim w b c s t | (s,t) | s IN e /\ t IN e } = e /\
  { chim w b d s t | (s,t) | s IN e /\ t IN e } = e ==>
  { chim w b (c INTER d) s t | (s,t) | s IN e /\ t IN e } = e
Proof
  strip_tac
  \\ qmatch_goalsub_abbrev_tac`chim w b cd _ _`
  \\ fs[Once EXTENSION]
  \\ gen_tac
  \\ Cases_on`x IN e` \\ simp[]
  >- (
    qexistsl_tac[`x`,`x`]
    \\ DEP_REWRITE_TAC[chim_same]
    \\ fs[SUBSET_DEF, Abbr`cd`] )
  \\ rpt gen_tac
  \\ Cases_on`s IN e /\ t IN e` \\ fs[]
  \\ qunabbrev_tac`cd`
  \\ DEP_REWRITE_TAC[chim_INTER]
  \\ conj_tac >- metis_tac[SUBSET_DEF]
  \\ last_x_assum(qspec_then`x`mp_tac)
  \\ simp[]
  \\ disch_then(qspecl_then[`chim w b d s t`,`t`]mp_tac)
  \\ disch_then(irule o CONTRAPOS)
  \\ simp[]
  \\ first_x_assum(qspec_then`chim w b d s t`(mp_tac o SYM))
  \\ simp[] \\ metis_tac[]
QED

Theorem chim_closed_BIGINTER:
  b factorises w /\ e SUBSET w ==>
  !sos. FINITE sos ==>
    sos <> {} /\
    (!c. c IN sos ==> c SUBSET b /\
         { chim w b c s t | (s,t) | s IN e /\ t IN e } = e)
   ==>
   { chim w b (BIGINTER sos) s t | (s,t) | s IN e /\ t IN e } = e
Proof
  strip_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ conj_tac >- simp[]
  \\ gen_tac \\ strip_tac
  \\ qx_gen_tac`c`
  \\ strip_tac \\ strip_tac
  \\ Cases_on`sos = {}` >- simp[]
  \\ rewrite_tac[BIGINTER_INSERT]
  \\ irule chim_closed_INTER
  \\ fs[]
  \\ irule BIGINTER_SUBSET
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Overload "trivial" = ``\s. !x y. x IN s /\ y IN s ==> x = y``

Theorem trivial_CARD:
  trivial s <=> FINITE s /\ CARD s <= 1
Proof
  Cases_on`s` \\ rw[]
  \\ Cases_on`t` \\ rw[]
  \\ gs[]
  \\ qmatch_goalsub_abbrev_tac`A <=> _`
  \\ Cases_on`A = T` >- (fs[Abbr`A`] \\ metis_tac[])
  \\ fs[]
  \\ CCONTR_TAC \\ gs[]
QED

Theorem trivial_empty_SING:
  trivial s <=> s = {} \/ SING s
Proof
  rw[trivial_CARD]
  \\ Cases_on`s` \\ simp[]
  \\ Cases_on`t` \\ simp[]
  \\ simp[INSERT_EQ_SING] \\ fs[]
  \\ CCONTR_TAC \\ gs[]
QED

Theorem factorises_trivial:
  trivial b ==>
  (b factorises w <=> b = if SING w then {} else {discrete_partition w})
Proof
  rw[trivial_CARD, EQ_IMP_THM] \\ gs[]
  >- (
    gs[factorises_def, partitions_SING]
    \\ Cases_on`b` \\ gs[]
    \\ Cases_on`t` \\ gs[]
    \\ gs[SING_DEF])
  >- (
    fs[factorises_alt]
    \\ fs[EXISTS_UNIQUE_THM]
    \\ metis_tac[trivial_empty_SING, SING_DEF, IN_INSERT])
  \\ Cases_on`w = {}` \\ gs[]
  \\ TRY (
    fs[factorises_def, partitions_empty]
    \\ TRY(Cases_on`b` \\ gs[])
    \\ TRY(Cases_on`t` \\ gs[])
    \\ simp[discrete_partition_def]
    \\ NO_TAC)
  >- (
    Cases_on`b` \\ gs[]
    >- (
      Cases_on`w` \\ gs[]
      \\ Cases_on`t` \\ gs[]
      \\ drule factorises_distinguish
      \\ simp[] \\ METIS_TAC[])
    \\ Cases_on`t` \\ gs[]
    \\ drule factorises_distinguish
    \\ simp[] \\ strip_tac
    \\ fs[factorises_alt]
    \\ Cases_on`?s a b. s IN x /\ a IN s /\ b IN s /\ a <> b`
    >- (
      fs[]
      \\ `a IN w /\ b IN w` by metis_tac[partitions_thm, SUBSET_DEF]
      \\ `part x a = part x b` by metis_tac[part_unique]
      \\ metis_tac[])
    \\ `!s. s IN x ==> SING s`
    by (
      rw[SING_DEF]
      \\ Cases_on`s` \\ fs[partitions_thm]
      >- metis_tac[]
      \\ Cases_on`t` \\ gs[]
      \\ metis_tac[IN_INSERT])
    \\ simp[discrete_partition_def]
    \\ simp[Once EXTENSION]
    \\ fs[partitions_thm, EXISTS_UNIQUE_THM, SUBSET_DEF]
    \\ rw[EQ_IMP_THM]
    >- (res_tac \\ fs[SING_DEF])
    \\ res_tac \\ fs[SING_DEF]
    \\ res_tac \\ fs[])
  \\ simp[factorises_alt, discrete_partition_partitions]
  \\ simp[Once discrete_partition_def]
  \\ simp[Once SET_EQ_SUBSET]
  \\ conj_tac >- metis_tac[SING_DEF]
  \\ rw[EXISTS_UNIQUE_THM] >- metis_tac[]
  \\ gs[part_discrete_partition]
QED

Theorem factorises_FINITE:
  b factorises w /\ FINITE w ==> FINITE b /\ EVERY_FINITE b
Proof
  rw[factorises_def]
  \\ irule SUBSET_FINITE
  THENL [qexists_tac`POW (POW w)`, qexists_tac`POW w`]
  \\ simp[SUBSET_DEF] \\ simp[IN_POW]
  \\ fs[partitions_thm]
  \\ TRY(simp[SUBSET_DEF] \\ CHANGED_TAC(simp[IN_POW]))
  \\ metis_tac[]
QED

Theorem factorises_CARD:
  b factorises w /\ FINITE w ==> CARD w = PROD_IMAGE CARD b
Proof
  strip_tac
  \\ imp_res_tac factorises_FINITE
  \\ imp_res_tac FINITE_BIGPROD
  \\ `CARD w = CARD (BIGPROD b)` by metis_tac[factorises_def, FINITE_BIJ_CARD]
  \\ simp[CARD_BIGPROD]
QED

Theorem factorises_small_or_prime:
  b factorises w /\ FINITE w /\ (CARD w <= 1 \/ prime (CARD w)) ==>
  trivial b
Proof
  strip_tac
  >- (
    Cases_on`w` \\ gs[]
    >- fs[factorises_alt, partitions_empty]
    \\ Cases_on`t` \\ gs[]
    \\ fs[factorises_alt, partitions_SING] )
  \\ imp_res_tac factorises_CARD
  \\ imp_res_tac factorises_FINITE
  \\ fs[prime_PROD_IMAGE]
  \\ simp[trivial_empty_SING]
  \\ Cases_on`b = {}` \\ gs[]
  \\ Cases_on`w = {}` \\ fs[PROD_IMAGE_EQ_0]
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[ONE_NOT_ZERO, NOT_PRIME_0])
  \\ `!v. v IN b ==> 1 < CARD v`
  by (
    rw[]
    \\ fs[factorises_def]
    \\ res_tac
    \\ Cases_on`v = {}` \\ fs[]
    \\ Cases_on`SING v`
    >- ( fs[SING_DEF] \\ fs[SING_partitions] )
    \\ Cases_on`v` \\ gs[]
    \\ Cases_on`t` \\ gs[] )
  \\ gs[SUBSET_DEF, PULL_EXISTS]
  \\ `!v. v IN b ==> CARD v = p` by metis_tac[LESS_REFL]
  \\ simp[SING_DEF]
  \\ simp[Once EXTENSION]
  \\ fs[EXISTS_UNIQUE_THM]
  \\ qexists_tac`x`
  \\ rw[EQ_IMP_THM]
QED

Theorem factorises_empty[simp]:
  b factorises {} <=> b = {{}}
Proof
  rw[EQ_IMP_THM]
  >- (
    drule factorises_small_or_prime
    \\ simp[]
    \\ strip_tac
    \\ fs[factorises_trivial]
    \\ rw[discrete_partition_def])
  \\ DEP_REWRITE_TAC[factorises_trivial]
  \\ simp[discrete_partition_def]
QED

Theorem empty_factorises:
  {} factorises w <=> SING w
Proof
  rw[factorises_alt, SING_DEF, EXTENSION]
  \\ metis_tac[]
QED

Theorem factorises_SING:
  SING w ==>
    (b factorises w <=> b = {})
Proof
  rw[EQ_IMP_THM, empty_factorises]
  \\ drule factorises_small_or_prime
  \\ fs[SING_IFF_CARD1]
  \\ strip_tac
  \\ fs[factorises_trivial]
  \\ simp[SING_IFF_CARD1]
QED

Theorem factorises_SING_alt[simp]:
  b factorises {x} <=> b = {}
Proof
  metis_tac[factorises_SING, SING_DEF]
QED

Theorem factorises_prime:
  b factorises w /\ FINITE w /\ prime (CARD w) ==> SING b
Proof
  strip_tac
  \\ drule factorises_small_or_prime
  \\ rw[]
  \\ fs[trivial_empty_SING]
  \\ fs[empty_factorises]
  \\ gs[SING_IFF_CARD1]
QED

Theorem factorises_PROD_primes:
  b factorises w /\ FINITE w /\
  CARD w = PROD ps /\ EVERY prime ps /\ 2 <= LENGTH ps ==>
  1 <= CARD b /\ CARD b <= LENGTH ps
Proof
  strip_tac
  \\ Cases_on`b = {}`
  >- (
    fs[empty_factorises]
    \\ gs[SING_IFF_CARD1]
    \\ gs[PROD_eq_1]
    \\ Cases_on`ps` \\ fs[]
    \\ metis_tac[NOT_PRIME_1])
  \\ imp_res_tac factorises_FINITE
  \\ conj_tac >- (Cases_on`b` \\ gs[])
  \\ Cases_on`w = {}` >- gs[]
  \\ drule factorises_CARD \\ rw[]
  \\ `!v. v IN b ==> 2 <= CARD v`
  by (
    rw[]
    \\ fs[factorises_def]
    \\ Cases_on`v = {}` >- metis_tac[empty_partitions]
    \\ Cases_on`SING v` >- metis_tac[SING_partitions, SING_DEF]
    \\ res_tac
    \\ Cases_on`v` \\ gs[]
    \\ Cases_on`t` \\ gs[])
  \\ gs[PROD_IMAGE_eq_PROD_MAP_SET_TO_LIST]
  \\ qmatch_asmsub_abbrev_tac`PROD ps = PROD qs`
  \\ `CARD b = LENGTH qs` by simp[Abbr`qs`, SET_TO_LIST_CARD]
  \\ `!x. MEM x qs ==> 2 <= x` by simp[Abbr`qs`, MEM_MAP, PULL_EXISTS]
  \\ qspecl_then[`ps`,`1`]mp_tac BAG_GEN_PROD_LIST_TO_BAG
  \\ simp[]
  \\ qspec_then`PROD qs`mp_tac PRIME_FACTORIZATION
  \\ impl_keep_tac
  >- (
    CCONTR_TAC \\ fs[PROD_EQ_0, EVERY_MEM]
    \\ res_tac \\ fs[] )
  \\ disch_then(qspec_then`LIST_TO_BAG ps`mp_tac)
  \\ simp[IN_LIST_TO_BAG, GSYM EVERY_MEM]
  \\ ntac 2 strip_tac \\ fs[]
  \\ Cases_on`EVERY prime qs`
  >- (
    qspecl_then[`qs`,`1`]mp_tac BAG_GEN_PROD_LIST_TO_BAG
    \\ simp[] \\ strip_tac
    \\ qspec_then`PROD qs`mp_tac PRIME_FACTORIZATION
    \\ simp[]
    \\ disch_then(qspec_then`LIST_TO_BAG qs`mp_tac)
    \\ simp[IN_LIST_TO_BAG, GSYM EVERY_MEM]
    \\ metis_tac[PERM_LIST_TO_BAG, PERM_LENGTH, LESS_OR_EQ])
  \\ rw[] \\ CCONTR_TAC \\ fs[NOT_LESS_EQUAL]
  \\ qspecl_then[`LIST_TO_BAG qs`,`PROD qs`]mp_tac
       LESS_EQ_BAG_CARD_PRIME_FACTORS_PROD
  \\ simp[]
  \\ qpat_x_assum`_ = PRIME_FACTORS _`(assume_tac o SYM)
  \\ simp[]
  \\ simp[BAG_GEN_PROD_LIST_TO_BAG]
  \\ simp[IN_LIST_TO_BAG]
QED

Definition generates_partition_def:
  generates_partition w b c v <=>
    b factorises w /\ c SUBSET b /\ v partitions w /\
    !s. s IN v ==> { chim w b c x y | (x, y) | x IN s /\ y IN w } = s
End

Theorem generates_partition_subsets:
  generates_partition w b c v <=>
    b factorises w /\ c SUBSET b /\ v partitions w /\
    !s. s IN v ==> { chim w b c x y | (x, y) | x IN s /\ y IN w } SUBSET s
Proof
  rw[generates_partition_def, EQ_IMP_THM]
  \\ rw[Once SET_EQ_SUBSET]
  \\ rw[SUBSET_DEF]
  \\ qexistsl_tac[`x`,`x`]
  \\ reverse conj_asm2_tac >- metis_tac[partitions_thm, SUBSET_DEF]
  \\ irule (GSYM chim_same)
  \\ simp[]
QED

Theorem generates_partition_subsets_parts:
  generates_partition w b c v <=>
    b factorises w /\ c SUBSET b /\ v partitions w /\
    !s t. s IN v /\ t IN v ==>
      { chim w b c x y | (x, y) | x IN s /\ y IN t } SUBSET s
Proof
  simp[generates_partition_subsets]
  \\ rw[EQ_IMP_THM]
  \\ imp_res_tac partitions_thm
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[EXISTS_UNIQUE_THM]
QED

Theorem generates_partition_in_parts:
  generates_partition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ v partitions w ∧
    ∀x y. x ∈ w ∧ y ∈ w ⇒ chim w b c x y ∈ part v x
Proof
  simp[generates_partition_subsets]
  \\ rw[EQ_IMP_THM]
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ first_x_assum irule
    \\ metis_tac[part_in_partition, in_part])
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qx_genl_tac[`x`,`y`] \\ strip_tac
  \\ `x ∈ w` by metis_tac[partitions_thm, SUBSET_DEF]
  \\ `s = part v x` by metis_tac[part_unique] \\ rw[]
QED

Theorem generates_partition_same_parts:
  generates_partition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ v partitions w ∧
    ∀x y. x ∈ w ∧ y ∈ w ⇒ part v (chim w b c x y) = part v x
Proof
  rw[generates_partition_in_parts]
  \\ reverse(rw[EQ_IMP_THM])
  >- (
    `chim w b c x y ∈ w` by metis_tac[chim_thm]
    \\ metis_tac[in_part])
  \\ irule EQ_SYM
  \\ irule part_unique
  \\ metis_tac[chim_thm, in_part, part_in_partition]
QED

Theorem generates_partition_common_refinement_refines:
  generates_partition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ v partitions w ∧
    common_refinement w c refines v
Proof
  rw[generates_partition_same_parts]
  \\ rw[EQ_IMP_THM]
  >- (
    DEP_REWRITE_TAC[refines_grows_parts]
    \\ simp[common_refinement_partitions]
    \\ rw[]
    \\ `chim w b c x y = y` suffices_by metis_tac[]
    \\ `chim w b c x y ∈ w` by metis_tac[chim_thm]
    \\ `∀v. v ∈ b ⇒ part v (chim w b c x y) = part v y`
    suffices_by metis_tac[factorises_distinguish]
    \\ qx_gen_tac`z`
    \\ rw[chim_thm]
    \\ `common_refinement w c refines z` by (
      irule common_refinement_refines
      \\ fs[SUBSET_DEF, factorises_def])
    \\ `z partitions w` by metis_tac[factorises_def]
    \\ metis_tac[common_refinement_partitions, refines_grows_parts])
  \\ `common_refinement w c partitions w`
  by metis_tac[common_refinement_partitions]
  \\ `∀v. v ∈ c ⇒ v partitions w` by metis_tac[SUBSET_DEF, factorises_def]
  \\ `chim w b c x y ∈ w` by metis_tac[chim_thm]
  \\ `part (common_refinement w c) (chim w b c x y) =
      part (common_refinement w c) x`
  suffices_by metis_tac[refines_grows_parts]
  \\ irule same_part_common_refinement
  \\ gs[SUBSET_DEF] \\ rw[chim_thm]
QED

Theorem refines_generates_partition:
  v2 partitions w ∧
  v1 refines v2 ∧ generates_partition w b c v1 ⇒
  generates_partition w b c v2
Proof
  strip_tac
  \\ gs[generates_partition_common_refinement_refines]
  \\ metis_tac[refines_transitive]
QED

Theorem generates_common_refinement:
  b factorises w ∧ c ⊆ b ∧
  (∀v. v ∈ sop ⇒ generates_partition w b c v)
  ⇒
  generates_partition w b c (common_refinement w sop)
Proof
  strip_tac
  \\ fsrw_tac[DNF_ss][]
  \\ gs[generates_partition_common_refinement_refines,
        common_refinement_partitions]
  \\ irule refines_common_refinement
  \\ simp[common_refinement_partitions]
QED

Theorem factorises_generates_any_partition:
  b factorises w ∧ v partitions w ⇒
  generates_partition w b b v
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[generates_partition_common_refinement_refines]
  \\ simp[]
  \\ simp[factorises_common_refinement_discrete]
  \\ simp[discrete_refines]
QED

Theorem empty_generates_indiscrete_partition:
  b factorises w ==>
  (generates_partition w b {} v <=> v = indiscrete_partition w)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[generates_partition_common_refinement_refines]
  \\ simp[common_refinement_empty]
  \\ rw[EQ_IMP_THM]
  \\ metis_tac[refines_indiscrete, refines_antisym,
               indiscrete_partition_partitions]
QED

Theorem generates_partition_SUBSET:
  d ⊆ b ∧ c ⊆ d ∧ generates_partition w b c v ⇒
  generates_partition w b d v
Proof
  strip_tac
  \\ `c SUBSET b` by metis_tac[SUBSET_TRANS]
  \\ gs[generates_partition_common_refinement_refines]
  \\ irule refines_transitive
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule common_refinement_SUBSET
  \\ fs[SUBSET_DEF, factorises_def]
QED

Theorem INTER_generates_partition:
  generates_partition w b c v ∧
  generates_partition w b d v
  ⇒
  generates_partition w b (c INTER d) v
Proof
  simp[generates_partition_same_parts]
  \\ strip_tac
  \\ conj_tac >- fs[SUBSET_DEF]
  \\ drule chim_INTER
  \\ simp[]
  \\ disch_then kall_tac
  \\ rpt strip_tac
  \\ `chim w b d x y ∈ w` by metis_tac[chim_thm]
  \\ metis_tac[]
QED

Definition history_def:
  history w b v =
    @h. generates_partition w b h v ∧
        (∀h'. generates_partition w b h' v ⇒ h ⊆ h')
End

Theorem history_thm:
  FINITE b ∧ b factorises w ∧ v partitions w ⇒
  generates_partition w b (history w b v) v ∧
  ∀h. generates_partition w b h v ⇒ (history w b v) ⊆ h
Proof
  strip_tac
  \\ simp[history_def]
  \\ SELECT_ELIM_TAC
  \\ reverse conj_tac >- metis_tac[]
  \\ qexists_tac`BIGINTER { h | generates_partition w b h v }`
  \\ qmatch_goalsub_abbrev_tac`generates_partition _ _ c _`
  \\ reverse conj_asm2_tac >- rw[SUBSET_DEF, Abbr`c`]
  \\ qmatch_asmsub_abbrev_tac`BIGINTER s`
  \\ `FINITE s`
  by (
    irule SUBSET_FINITE
    \\ qexists_tac`POW b`
    \\ simp[Abbr`s`, Once SUBSET_DEF, IN_POW]
    \\ simp[generates_partition_def])
  \\ `!d. FINITE d ==> d <> {} ∧ d ⊆ s ⇒
        generates_partition w b (BIGINTER d) v`
  suffices_by (
    strip_tac
    \\ qunabbrev_tac`c`
    \\ first_x_assum irule
    \\ simp[Abbr`s`]
    \\ simp[Once EXTENSION]
    \\ metis_tac[factorises_generates_any_partition])
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[] \\ gs[]
  \\ Cases_on`d = {}` \\ gs[]
  >- fs[Abbr`s`, EXTENSION]
  \\ irule INTER_generates_partition
  \\ fs[Abbr`s`]
QED

Theorem refines_history:
  FINITE b ∧ b factorises w ∧
  x partitions w ∧ y partitions w ∧
  x refines y ⇒
  history w b y ⊆ history w b x
Proof
  strip_tac
  \\ drule history_thm
  \\ disch_then drule
  \\ disch_then(qspec_then`y`mp_tac)
  \\ simp[] \\ strip_tac
  \\ first_x_assum irule
  \\ irule refines_generates_partition
  \\ metis_tac[history_thm]
QED

Theorem history_eq_empty:
  FINITE b ∧ b factorises w ∧ v partitions w ⇒
  (history w b v = {} <=> v = indiscrete_partition w)
Proof
  strip_tac
  \\ drule history_thm
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[EQ_IMP_THM]
  \\ gs[empty_generates_indiscrete_partition]
  \\ first_x_assum(qspec_then`{}`mp_tac)
  \\ simp[] \\ disch_then irule
  \\ simp[empty_generates_indiscrete_partition]
QED

Theorem history_SUBSET_factorisation:
  FINITE b ∧ b factorises w ∧ v partitions w ⇒
  history w b v ⊆ b
Proof
  strip_tac
  \\ imp_res_tac history_thm
  \\ fs[generates_partition_def]
QED

Theorem imp_history_SUBSET:
  FINITE b ∧ b factorises w ∧ v partitions w ∧
  generates_partition w b h v ⇒ history w b v ⊆ h
Proof
  strip_tac
  \\ drule history_thm
  \\ rw[]
QED

Theorem history_partitions:
  FINITE b ∧ b factorises w ∧ v partitions w ∧ h ∈ history w b v ⇒
  h partitions w
Proof
  strip_tac
  \\ imp_res_tac history_thm
  \\ fs[generates_partition_def]
  \\ fs[factorises_def, SUBSET_DEF]
QED

Theorem history_common_refinement:
  !sop. FINITE sop ==>
  FINITE b ∧ b factorises w ∧ (!v. v IN sop ==> v partitions w) ==>
  history w b (common_refinement w sop) = BIGUNION (IMAGE (history w b) sop)
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ rw[common_refinement_empty, history_eq_empty,
        indiscrete_partition_partitions]
  \\ gs[]
  \\ simp[Once SET_EQ_SUBSET, BIGUNION_SUBSET, PULL_EXISTS]
  \\ conj_tac
  >- (
    irule imp_history_SUBSET
    \\ simp[common_refinement_partitions]
    \\ irule generates_common_refinement
    \\ simp[history_SUBSET_factorisation, BIGUNION_SUBSET, PULL_EXISTS]
    \\ dsimp[]
    \\ conj_tac
    >- (
      irule generates_partition_SUBSET
      \\ simp[history_SUBSET_factorisation, BIGUNION_SUBSET, PULL_EXISTS]
      \\ qexists_tac`history w b e`
      \\ simp[history_thm])
    \\ simp[generates_partition_common_refinement_refines]
    \\ simp[history_SUBSET_factorisation, BIGUNION_SUBSET, PULL_EXISTS]
    \\ rw[]
    \\ irule refines_transitive
    \\ qexists_tac`common_refinement w (BIGUNION (IMAGE (history w b) sop))`
    \\ conj_tac
    >- (
      irule common_refinement_SUBSET
      \\ dsimp[PULL_EXISTS]
      \\ metis_tac[history_partitions])
    \\ irule refines_transitive
    \\ qexists_tac`common_refinement w (history w b v)`
    \\ conj_tac
    >- (
      irule common_refinement_SUBSET
      \\ simp[SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[history_partitions])
    \\ drule history_thm
    \\ disch_then drule
    \\ disch_then(qspec_then`v`mp_tac)
    \\ simp[generates_partition_common_refinement_refines])
  \\ conj_tac
  >- (
    irule imp_history_SUBSET
    \\ simp[]
    \\ irule refines_generates_partition
    \\ simp[]
    \\ qexists_tac`common_refinement w (e INSERT sop)`
    \\ conj_tac
    >- (
      irule common_refinement_refines
      \\ simp[] \\ metis_tac[] )
    \\ metis_tac[history_thm, common_refinement_partitions])
  \\ rw[]
  \\ irule imp_history_SUBSET
  \\ simp[]
  \\ irule refines_generates_partition
  \\ simp[]
  \\ qexists_tac`common_refinement w (e INSERT sop)`
  \\ conj_tac
  >- (
    irule common_refinement_refines
    \\ simp[] \\ metis_tac[] )
  \\ metis_tac[history_thm, common_refinement_partitions]
QED

Theorem SING_generates_partition:
  b factorises w ∧ v ∈ b ⇒
  generates_partition w b {v} v
Proof
  rw[generates_partition_common_refinement_refines]
  >- fs[factorises_def]
  \\ irule common_refinement_refines
  \\ fs[factorises_def]
QED

Theorem history_of_factor:
  FINITE b ∧ b factorises w ∧ v ∈ b ⇒
  history w b v = if w = {} then {} else {v}
Proof
  strip_tac
  \\ drule history_thm
  \\ disch_then drule
  \\ `v partitions w` by fs[factorises_def]
  \\ disch_then drule
  \\ `generates_partition w b {v} v` by metis_tac[SING_generates_partition]
  \\ strip_tac
  \\ `history w b v ⊆ {v}` by metis_tac[]
  \\ IF_CASES_TAC
  >- (
    rw[history_eq_empty]
    \\ fs[partitions_empty]
    \\ rw[indiscrete_partition_def])
  \\ Cases_on`v = {}`
  >- fs[empty_partitions]
  \\ `v <> indiscrete_partition w`
  by ( rw[indiscrete_partition_def] \\ fs[factorises_def] )
  \\ `history w b v <> {}`
  by metis_tac[empty_generates_indiscrete_partition, SUBSET_EMPTY]
  \\ rw[SET_EQ_SUBSET]
  \\ fs[SUBSET_DEF, GSYM MEMBER_NOT_EMPTY]
  \\ metis_tac[]
QED

Definition orthogonal_def:
  orthogonal w b x y <=>
    DISJOINT (history w b x) (history w b y)
End

Theorem orthogonal_via_refinement:
  FINITE b ∧ b factorises w ∧ x partitions w ∧ y partitions w ⇒
  (orthogonal w b x y <=>
  ?c. c ⊆ b ∧
      common_refinement w c refines x ∧
      common_refinement w (b DIFF c) refines y)
Proof
  strip_tac
  \\ rw[orthogonal_def, EQ_IMP_THM]
  >- (
    qexists_tac`history w b x`
    \\ simp[history_SUBSET_factorisation]
    \\ drule history_thm
    \\ disch_then drule
    \\ strip_tac
    \\ gs[generates_partition_common_refinement_refines,
          history_SUBSET_factorisation]
    \\ irule refines_transitive
    \\ qexists_tac`common_refinement w (history w b y)`
    \\ gs[generates_partition_common_refinement_refines,
          history_SUBSET_factorisation]
    \\ irule common_refinement_SUBSET
    \\ conj_tac >- fs[factorises_alt]
    \\ fs[SUBSET_DEF, IN_DISJOINT]
    \\ metis_tac[history_SUBSET_factorisation, SUBSET_DEF])
  \\ `b DIFF c ⊆ b` by simp[SUBSET_DEF]
  \\ `generates_partition w b c x ∧
      generates_partition w b (b DIFF c) y`
  by metis_tac[generates_partition_common_refinement_refines]
  \\ `history w b x ⊆ c ∧ history w b y ⊆ b DIFF c`
  by metis_tac[imp_history_SUBSET]
  \\ fs[SUBSET_DEF, IN_DISJOINT]
  \\ metis_tac[]
QED

Theorem orthogonal_sym:
  orthogonal w b x y <=> orthogonal w b y x
Proof
  rw[orthogonal_def, DISJOINT_SYM]
QED

Theorem orthogonal_refines:
  FINITE b ∧ b factorises w ∧ x partitions w ∧ y partitions w ∧
  orthogonal w b x z ∧ x refines y ⇒
  orthogonal w b y z
Proof
  rw[orthogonal_def]
  \\ drule refines_history
  \\ disch_then(first_assum o mp_then (Pat`(refines)`) mp_tac)
  \\ disch_then drule
  \\ fs[IN_DISJOINT, SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem common_refinement_orthogonal:
  FINITE sop ∧ FINITE b ∧ b factorises w ∧
  (!v. v IN sop ==> v partitions w ∧ orthogonal w b v z) ==>
  orthogonal w b (common_refinement w sop) z
Proof
  rw[orthogonal_def]
  \\ qspec_then`sop`(drule o UNDISCH) history_common_refinement
  \\ simp[PULL_EXISTS]
QED

Theorem orthogonal_indiscrete_refl:
  FINITE b ∧ b factorises w ∧ v partitions w ⇒
  (orthogonal w b v v <=> v = indiscrete_partition w)
Proof
  rw[orthogonal_def, history_eq_empty]
QED

Overload "before" = ``λw b x y. history w b x ⊆ history w b y``

Theorem common_refinement_refines_history_SUBSET:
  FINITE b ∧ b factorises w ∧ x partitions w ∧ c ⊆ b ⇒
  (common_refinement w c refines x <=> history w b x ⊆ c)
Proof
  strip_tac
  \\ rw[EQ_IMP_THM]
  >- (
    irule imp_history_SUBSET
    \\ rw[generates_partition_common_refinement_refines])
  \\ drule history_thm
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[generates_partition_common_refinement_refines]
  \\ irule refines_transitive
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule common_refinement_SUBSET
  \\ fs[factorises_def, SUBSET_DEF]
QED

Theorem before_via_refinement:
  FINITE b ∧
  b factorises w ∧ x partitions w ∧ y partitions w ⇒
  (before w b x y <=> !c. c ⊆ b ∧ common_refinement w c refines y ⇒
                                  common_refinement w c refines x)
Proof
  strip_tac
  \\ rw[EQ_IMP_THM]
  >- metis_tac[common_refinement_refines_history_SUBSET, SUBSET_TRANS]
  \\ first_x_assum(qspec_then`history w b y`mp_tac)
  \\ simp[history_SUBSET_factorisation]
  \\ DEP_REWRITE_TAC[common_refinement_refines_history_SUBSET]
  \\ simp[history_SUBSET_factorisation]
QED

Theorem before_least_orthogonal:
  FINITE b ∧ b factorises w ∧ x partitions w ∧ y partitions w ⇒
  (before w b x y <=> ∀z. z partitions w ∧ orthogonal w b y z ⇒
                                           orthogonal w b x z)
Proof
  strip_tac
  \\ eq_tac
  >- (
    rw[orthogonal_def, IN_DISJOINT]
    \\ fs[SUBSET_DEF]
    \\ metis_tac[])
  \\ Cases_on`w = {}` >- gs[]
  \\ rw[]
  \\ CCONTR_TAC
  \\ fs[SUBSET_DEF]
  \\ qmatch_asmsub_rename_tac`z ∈ _`
  \\ `z ∈ b` by metis_tac[SUBSET_DEF, history_SUBSET_factorisation]
  \\ `z ≠ {}` by metis_tac[factorises_def, empty_partitions]
  \\ `history w b z = {z}` by metis_tac[history_of_factor]
  \\ fs[orthogonal_def, IN_DISJOINT]
  \\ first_x_assum(qspec_then`z`mp_tac)
  \\ simp[] \\ fs[factorises_def]
QED

Theorem before_refl:
  before w b x x
Proof
  rw[]
QED

Theorem before_trans:
  before w b x y ∧ before w b y z ⇒ before w b x z
Proof
  metis_tac[SUBSET_TRANS]
QED

Theorem refines_before = refines_history

Theorem common_refinement_before:
  FINITE sop ∧ FINITE b ∧ b factorises w ∧ z partitions w ∧
  (!v. v IN sop ==> v partitions w ∧ before w b v z) ==>
  before w b (common_refinement w sop) z
Proof
  rw[history_common_refinement]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Theorem history_as_factors_before:
  FINITE b ∧ b factorises w ∧ x partitions w ⇒
  history w b x = if w = {} then {} else { v | v ∈ b ∧ before w b v x }
Proof
  IF_CASES_TAC
  >- (
    simp[history_eq_empty]
    \\ rw[indiscrete_partition_def])
  \\ strip_tac
  \\ simp[Once EXTENSION]
  \\ qx_gen_tac`z`
  \\ reverse(Cases_on`z ∈ b` \\ simp[])
  >- metis_tac[history_SUBSET_factorisation, SUBSET_DEF]
  \\ simp[history_of_factor]
QED

Definition generates_subpartition_def:
  generates_subpartition w b c v <=>
  b factorises w ∧ c ⊆ b ∧ is_subpartition w v ∧
  ∀s. s ∈ v ⇒ {chim w b c x y | (x,y) | x ∈ s ∧ y ∈ subpart_domain w v} = s
End

Theorem generates_partition_subpartition:
  generates_partition w b c v ⇒ generates_subpartition w b c v
Proof
  rw[generates_partition_def, generates_subpartition_def]
  >- metis_tac[partition_is_subpartition]
  \\ rw[partition_is_subpartition]
QED

Theorem generates_subpartition_subsets:
  generates_subpartition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ is_subpartition w v ∧
    ∀s. s ∈ v ⇒ {chim w b c x y | (x,y) | x ∈ s ∧ y ∈ subpart_domain w v } ⊆ s
Proof
  rw[generates_subpartition_def]
  \\ rw[EQ_IMP_THM]
  \\ rw[SET_EQ_SUBSET]
  \\ rw[SUBSET_DEF]
  \\ qexistsl_tac[`x`,`x`]
  \\ `v partitions subpart_domain w v ∧ subpart_domain w v ⊆ w`
  by metis_tac[subpart_domain_thm]
  \\ `s ⊆ subpart_domain w v` by metis_tac[partitions_thm]
  \\ reverse conj_asm2_tac >- metis_tac[SUBSET_DEF]
  \\ irule (GSYM chim_same)
  \\ metis_tac[SUBSET_DEF]
QED

Theorem generates_subpartition_subsets_parts:
  generates_subpartition w b c v <=>
    b factorises w /\ c SUBSET b /\ is_subpartition w v /\
    !s t. s IN v /\ t IN v ==>
      { chim w b c x y | (x, y) | x IN s /\ y IN t } SUBSET s
Proof
  simp[generates_subpartition_subsets]
  \\ rw[EQ_IMP_THM]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ drule subpart_domain_thm
  \\ dsimp[EQ_IMP_THM]
  \\ rw[SUBSET_DEF]
  \\ first_x_assum irule
  \\ metis_tac[partitions_thm, SUBSET_DEF]
QED

Theorem generates_subpartition_in_parts:
  generates_subpartition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ is_subpartition w v ∧
    ∀x y. x ∈ subpart_domain w v ∧ y ∈ subpart_domain w v
          ⇒ chim w b c x y ∈ part v x
Proof
  simp[generates_subpartition_subsets]
  \\ rw[EQ_IMP_THM]
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ first_x_assum irule
    \\ drule subpart_domain_thm
    \\ dsimp[EQ_IMP_THM]
    \\ rpt strip_tac
    \\ metis_tac[part_in_partition, in_part])
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qx_genl_tac[`x`,`y`] \\ strip_tac
  \\ drule subpart_domain_thm
  \\ dsimp[EQ_IMP_THM]
  \\ rpt strip_tac
  \\ `x ∈ subpart_domain w v` by metis_tac[partitions_thm, SUBSET_DEF]
  \\ `s = part v x` by metis_tac[part_unique] \\ rw[]
QED

Theorem generates_subpartition_same_parts:
  generates_subpartition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ is_subpartition w v ∧
    ∀x y. x ∈ subpart_domain w v ∧ y ∈ subpart_domain w v ⇒
          chim w b c x y ∈ subpart_domain w v ∧
          part v (chim w b c x y) = part v x
Proof
  rw[generates_subpartition_in_parts, CONJ_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`A ∧ _`
  \\ Cases_on`A = T` \\ fs[Abbr`A`]
  \\ drule subpart_domain_thm \\ strip_tac
  \\ eq_tac \\ strip_tac \\ rpt gen_tac \\ strip_tac
  >- (
    conj_asm1_tac
    >- metis_tac[part_in_partition, partitions_thm, SUBSET_DEF]
    \\ irule EQ_SYM
    \\ irule part_unique
    \\ metis_tac[in_part, part_in_partition])
  >- (
    `chim w b c x y ∈ w` by metis_tac[chim_thm, SUBSET_DEF]
    \\ metis_tac[in_part])
QED

Theorem generates_subpartition_common_refinement_refines:
  generates_subpartition w b c v ⇔
    b factorises w ∧ c ⊆ b ∧ is_subpartition w v ∧
    restrict_partition (common_refinement w c) (subpart_domain w v) refines v ∧
    { chim w b c x y | (x,y) | {x; y} ⊆ subpart_domain w v } = subpart_domain w v
Proof
  rw[generates_subpartition_same_parts, CONJ_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`A ∧ _`
  \\ Cases_on`A = T` \\ fs[Abbr`A`]
  \\ eq_tac \\ strip_tac
  >- (
    simp[Once SET_EQ_SUBSET]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ reverse conj_tac
    >- (
      rw[]
      \\ qexistsl_tac[`x`,`x`]
      \\ reverse conj_tac >- simp[]
      \\ irule EQ_SYM
      \\ irule chim_same
      \\ metis_tac[subpart_domain_thm, partitions_thm, SUBSET_DEF])
    \\ `v partitions (subpart_domain w v)`
    by metis_tac[subpart_domain_thm]
    \\ `common_refinement w c partitions w`
    by metis_tac[common_refinement_partitions]
    \\ drule restrict_partition_partitions
    \\ disch_then(qspec_then`subpart_domain w v`mp_tac)
    \\ impl_keep_tac >- metis_tac[subpart_domain_thm]
    \\ strip_tac
    \\ qspec_then`subpart_domain w v`(fn th => DEP_REWRITE_TAC[th])
         refines_grows_parts
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`restrict_partition _ e`
    \\ rpt strip_tac
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[part_restrict_partition]
    \\ simp[]
    \\ `∀z. z ∈ c ⇒ common_refinement w c refines z`
    by (
      rw[]
      \\ irule common_refinement_refines
      \\ fs[SUBSET_DEF, factorises_def])
    \\ strip_tac
    \\ `part v (chim w b c x y) = part v y` suffices_by metis_tac[]
    \\ `part (common_refinement w c) x = part (common_refinement w c) y`
    by (
      irule part_unique
      \\ conj_tac
      >- (
        fs[Once EXTENSION]
        \\ first_x_assum(qspec_then`y`mp_tac)
        \\ simp[]
        \\ strip_tac \\ irule in_part
        \\ metis_tac[SUBSET_DEF])
      \\ conj_tac >- metis_tac[part_in_partition, SUBSET_DEF]
      \\ metis_tac[SUBSET_DEF])
    \\ `∀z. z ∈ c ⇒ part z x = part z y`
    by (
      rw[]
      \\ `z partitions w` by metis_tac[factorises_def, SUBSET_DEF]
      \\ `x ∈ w ∧ y ∈ w` by metis_tac[SUBSET_DEF]
      \\ metis_tac[refines_grows_parts])
    \\ `chim w b c x y = y` suffices_by metis_tac[]
    \\ `chim w b c x y ∈ w` by metis_tac[chim_thm, SUBSET_DEF]
    \\ `y ∈ w` by metis_tac[SUBSET_DEF]
    \\ `∀v. v ∈ b ⇒ part v (chim w b c x y) = part v y`
    suffices_by metis_tac[factorises_distinguish]
    \\ `x ∈ w` by metis_tac[SUBSET_DEF]
    \\ simp[chim_thm]
    \\ rw[])
  \\ rpt gen_tac \\ strip_tac
  \\ `common_refinement w c partitions w`
  by metis_tac[common_refinement_partitions]
  \\ qmatch_asmsub_abbrev_tac`restrict_partition _ e`
  \\ `e ⊆ w` by metis_tac[subpart_domain_thm]
  \\ drule restrict_partition_partitions
  \\ disch_then drule \\ strip_tac
  \\ drule refines_grows_parts
  \\ `v partitions e` by metis_tac[subpart_domain_thm]
  \\ disch_then drule \\ simp[]
  \\ disch_then(qspecl_then[`chim w b c x y`,`x`]mp_tac) \\ simp[]
  \\ DEP_REWRITE_TAC[part_restrict_partition]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    qpat_x_assum`_ = e`(SUBST1_TAC o SYM)
    \\ simp[] \\ metis_tac[] )
  \\ simp[]
  \\ disch_then irule
  \\ `part (common_refinement w c) (chim w b c x y) =
      part (common_refinement w c) x`
  by (
    irule same_part_common_refinement
    \\ reverse conj_tac >- metis_tac[SUBSET_DEF]
    \\ drule chim_thm
    \\ disch_then(qspecl_then[`y`,`x`,`c`]mp_tac)
    \\ impl_tac >- metis_tac[SUBSET_DEF]
    \\ rw[]
    \\ metis_tac[SUBSET_DEF])
  \\ simp[]
QED

Theorem refines_generates_subpartition:
  is_subpartition w v2 ∧ subpart_domain w v1 = subpart_domain w v2 ∧
  v1 refines v2 ∧ generates_subpartition w b c v1 ⇒
  generates_subpartition w b c v2
Proof
  strip_tac
  \\ gs[generates_subpartition_common_refinement_refines]
  \\ metis_tac[refines_transitive]
QED

Theorem generates_common_refinement_subpartitions:
  b factorises w ∧ c ⊆ b ∧ e ⊆ w ∧ sop <> {} ∧
  (∀v. v ∈ sop ⇒ generates_subpartition w b c v ∧
                  subpart_domain w v = e)
  ⇒
  generates_subpartition w b c (common_refinement e sop)
Proof
  strip_tac
  \\ gs[generates_subpartition_common_refinement_refines,
        is_subpartition_common_refinement]
  \\ reverse conj_tac
  >- (
    gs[GSYM MEMBER_NOT_EMPTY]
    \\ res_tac
    \\ BasicProvers.VAR_EQ_TAC
    \\ simp[] )
  \\ irule refines_common_refinement
  \\ `common_refinement w c partitions w` by simp[common_refinement_partitions]
  \\ reverse conj_tac >- metis_tac[restrict_partition_partitions]
  \\ qx_gen_tac`v` \\ strip_tac
  \\ first_x_assum drule
  \\ strip_tac
  \\ conj_asm1_tac >- metis_tac[subpart_domain_thm]
  \\ fs[]
QED

Theorem factorises_generates_any_subpartition:
  b factorises w ∧ is_subpartition w v ⇒
  generates_subpartition w b b v
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[generates_subpartition_common_refinement_refines]
  \\ simp[]
  \\ simp[factorises_common_refinement_discrete]
  \\ DEP_REWRITE_TAC[restrict_discrete_partition]
  \\ conj_asm1_tac >- metis_tac[subpart_domain_thm]
  \\ conj_asm1_tac >- metis_tac[discrete_refines, subpart_domain_thm]
  \\ simp[Once EXTENSION]
  \\ rw[EQ_IMP_THM] \\ gs[SUBSET_DEF]
  \\ qexistsl_tac[`x`,`x`]
  \\ simp[]
QED

Theorem empty_generates_indiscrete_subpartition:
  b factorises w ==>
  (generates_subpartition w b {} v <=>
   v = indiscrete_partition (subpart_domain w v) ∧
   is_subpartition w v)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[generates_subpartition_common_refinement_refines]
  \\ simp[common_refinement_empty]
  \\ Cases_on`is_subpartition w v` \\ simp[]
  \\ DEP_REWRITE_TAC[restrict_indiscrete_partition]
  \\ conj_asm1_tac >- metis_tac[subpart_domain_thm]
  \\ `v partitions (subpart_domain w v)` by metis_tac[subpart_domain_thm]
  \\ drule refines_indiscrete \\ strip_tac
  \\ rw[EQ_IMP_THM]
  >- metis_tac[refines_antisym, indiscrete_partition_partitions]
  >- metis_tac[refines_refl]
  \\ drule chim_empty
  \\ CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(RAND_CONV(SIMP_CONV(srw_ss())[]))))
  \\ simp[SET_EQ_SUBSET]
  \\ gs[SUBSET_DEF, PULL_EXISTS]
  \\ strip_tac
  \\ metis_tac[]
QED

Theorem UNION_generates_subpartition:
  generates_subpartition w b c v ∧
  generates_subpartition w b d v
  ⇒
  generates_subpartition w b (c ∪ d) v
Proof
  strip_tac
  \\ gs[generates_subpartition_in_parts]
  \\ rpt strip_tac
  \\ drule chim_UNION
  \\ disch_then(qspecl_then[`y`,`x`,`d`,`c`]mp_tac)
  \\ impl_keep_tac >- metis_tac[subpart_domain_thm, SUBSET_DEF]
  \\ simp[] \\ disch_then kall_tac
  \\ first_x_assum irule
  \\ simp[]
  \\ `v partitions (subpart_domain w v)` by metis_tac[subpart_domain_thm]
  \\ `part v x ∈ v` by metis_tac[part_in_partition]
  \\ `part v x ⊆ subpart_domain w v` by metis_tac[partitions_thm]
  \\ metis_tac[SUBSET_DEF]
QED

Theorem INTER_generates_subpartition:
  generates_subpartition w b c v ∧
  generates_subpartition w b d v
  ⇒
  generates_subpartition w b (c INTER d) v
Proof
  strip_tac
  \\ gs[generates_subpartition_in_parts]
  \\ rpt strip_tac
  >- gs[SUBSET_DEF]
  \\ drule chim_INTER
  \\ disch_then(qspecl_then[`y`,`x`,`d`,`c`]mp_tac)
  \\ impl_keep_tac >- metis_tac[subpart_domain_thm, SUBSET_DEF]
  \\ simp[] \\ disch_then kall_tac
  \\ `chim w b d x y ∈ part v x` by metis_tac[]
  \\ `v partitions (subpart_domain w v)` by metis_tac[subpart_domain_thm]
  \\ `part v x ∈ v` by metis_tac[part_in_partition]
  \\ `part v x ⊆ subpart_domain w v` by metis_tac[partitions_thm]
  \\ `chim w b d x y ∈ subpart_domain w v` by metis_tac[SUBSET_DEF]
  \\ `chim w b c (chim w b d x y) y ∈ part v (chim w b d x y)`
  by metis_tac[]
  \\ `part v (chim w b d x y) = part v x` suffices_by metis_tac[]
  \\ irule EQ_SYM
  \\ irule part_unique
  \\ metis_tac[part_in_partition]
QED

Theorem generates_subpartition_SUBSET:
  generates_subpartition w b c v2 ∧
  is_subpartition w v1 ∧
  v1 ⊆ v2
  ⇒
  generates_subpartition w b c v1
Proof
  rw[generates_subpartition_subsets_parts]
  \\ gs[SUBSET_DEF, PULL_EXISTS]
  \\ metis_tac[]
QED

Definition subpart_history_def:
  subpart_history w b v =
  @h. generates_subpartition w b h v ∧
    ∀h'. generates_subpartition w b h' v ⇒ h ⊆ h'
End

Theorem subpart_history_thm:
  FINITE b ∧ b factorises w ∧ is_subpartition w v ⇒
  generates_subpartition w b (subpart_history w b v) v ∧
  ∀h. generates_subpartition w b h v ⇒ subpart_history w b v ⊆ h
Proof
  strip_tac
  \\ simp[subpart_history_def]
  \\ SELECT_ELIM_TAC
  \\ reverse conj_tac >- rw[]
  \\ qexists_tac`BIGINTER { h | generates_subpartition w b h v }`
  \\ qmatch_goalsub_abbrev_tac`generates_subpartition _ _ c _`
  \\ reverse conj_asm2_tac >- rw[SUBSET_DEF, Abbr`c`]
  \\ qmatch_asmsub_abbrev_tac`BIGINTER s`
  \\ `FINITE s`
  by (
    irule SUBSET_FINITE
    \\ qexists_tac`POW b`
    \\ simp[Abbr`s`, Once SUBSET_DEF, IN_POW]
    \\ simp[generates_subpartition_def])
  \\ `!d. FINITE d ==> d <> {} ∧ d ⊆ s ⇒
        generates_subpartition w b (BIGINTER d) v`
  suffices_by (
    strip_tac
    \\ qunabbrev_tac`c`
    \\ first_x_assum irule
    \\ simp[Abbr`s`]
    \\ simp[Once EXTENSION]
    \\ metis_tac[factorises_generates_any_subpartition])
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[] \\ gs[]
  \\ Cases_on`d = {}` \\ gs[]
  >- fs[Abbr`s`, EXTENSION]
  \\ irule INTER_generates_subpartition
  \\ fs[Abbr`s`]
QED

Theorem refines_subpart_history:
  FINITE b ∧ b factorises w ∧
  is_subpartition w x ∧ is_subpartition w y ∧
  subpart_domain w x = subpart_domain w y ∧
  x refines y ⇒
  subpart_history w b y ⊆ subpart_history w b x
Proof
  strip_tac
  \\ drule subpart_history_thm
  \\ disch_then drule
  \\ disch_then(qspec_then`y`mp_tac)
  \\ simp[] \\ strip_tac
  \\ first_x_assum irule
  \\ irule refines_generates_subpartition
  \\ metis_tac[subpart_history_thm]
QED

Theorem subpart_history_eq_empty:
  FINITE b ∧ b factorises w ∧ is_subpartition w v ⇒
  (subpart_history w b v = {} <=>
   v = indiscrete_partition (subpart_domain w v))
Proof
  strip_tac
  \\ drule subpart_history_thm
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[EQ_IMP_THM]
  \\ gs[empty_generates_indiscrete_subpartition]
  \\ first_x_assum(qspec_then`{}`mp_tac)
  \\ simp[] \\ disch_then irule
  \\ simp[empty_generates_indiscrete_subpartition]
QED

Theorem subpart_history_SUBSET_factorisation:
  FINITE b ∧ b factorises w ∧ is_subpartition w v ⇒
  subpart_history w b v ⊆ b
Proof
  strip_tac
  \\ imp_res_tac subpart_history_thm
  \\ fs[generates_subpartition_def]
QED

Theorem imp_subpart_history_SUBSET:
  FINITE b ∧ b factorises w ∧ is_subpartition w v ∧
  generates_subpartition w b h v ⇒ subpart_history w b v ⊆ h
Proof
  strip_tac
  \\ drule subpart_history_thm
  \\ rw[]
QED

Theorem SUBSET_subpart_history:
  FINITE b ∧ b factorises w ∧ is_subpartition w x ∧ is_subpartition w y ∧ x ⊆ y
  ⇒
  subpart_history w b x ⊆ subpart_history w b y
Proof
  strip_tac
  \\ irule imp_subpart_history_SUBSET
  \\ simp[]
  \\ irule generates_subpartition_SUBSET
  \\ metis_tac[subpart_history_thm]
QED

Theorem subpart_history_partitions:
  FINITE b ∧ b factorises w ∧ is_subpartition w v ∧
  h ∈ subpart_history w b v ⇒
  h partitions w
Proof
  strip_tac
  \\ imp_res_tac subpart_history_thm
  \\ fs[generates_subpartition_def]
  \\ fs[factorises_def, SUBSET_DEF]
QED

Theorem subpart_history_common_refinement_BIGUNION_SUBSET:
  FINITE b ∧ b factorises w ∧ e ⊆ w ∧
  (!v. v IN sop ==> is_subpartition w v ∧ subpart_domain w v = e) ==>
    BIGUNION (IMAGE (subpart_history w b) sop) ⊆
    subpart_history w b (common_refinement e sop)
Proof
  rw[]
  \\ rw[SUBSET_DEF]
  \\ qmatch_asmsub_rename_tac`s ∈ sop`
  \\ qpat_x_assum`x ∈ _`mp_tac
  \\ qid_spec_tac`x`
  \\ simp[GSYM SUBSET_DEF]
  \\ irule imp_subpart_history_SUBSET
  \\ simp[]
  \\ irule refines_generates_subpartition
  \\ simp[]
  \\ qexists_tac`common_refinement e sop`
  \\ `common_refinement e sop partitions e` by simp[common_refinement_partitions]
  \\ drule is_subpartition_common_refinement
  \\ disch_then(qspec_then`sop`strip_assume_tac)
  \\ simp[]
  \\ conj_tac
  >- (
    irule common_refinement_refines \\ simp[]
    \\ metis_tac[subpart_domain_thm])
  \\ metis_tac[subpart_history_thm]
QED

(*
Theorem factorises_count_4:
  x factorises count 4 ⇔
  x ∈ { { { {0}; {1}; {2}; {3} } };
        { { {0; 1}; {2; 3} };
          { {0; 2}; {1; 3} } };
        { { {0; 1}; {2; 3} };
          { {0; 3}; {1; 2} } };
        { { {0; 2}; {1; 3} };
          { {0; 3}; {1; 2} } } }
Proof
  rw[factorises_unique_inter]
  \\ reverse(rw[EQ_IMP_THM] \\ gs[PULL_EXISTS])
  \\ fsrw_tac[DNF_ss][]
  \\ TRY(simp[EXISTS_UNIQUE_THM] \\ NO_TAC)
  \\ TRY (
    qmatch_goalsub_abbrev_tac`_ ≠ {count 4}`
    \\ EVAL_TAC)
  \\ TRY (
    qmatch_goalsub_abbrev_tac`_ partitions count 4`
    \\ rw[partitions_thm, EXISTS_UNIQUE_THM]
    \\ dsimp[]
    \\ EVAL_TAC
    \\ gs[] )
  \\ `x factorises count 4`
  by simp[factorises_unique_inter, PULL_EXISTS]
  \\ drule factorises_CARD
  \\ simp[] \\ strip_tac
  \\ drule factorises_FINITE
  \\ simp[] \\ strip_tac
  \\ Cases_on`x` \\ fs[PROD_IMAGE_THM]
  \\ qmatch_asmsub_rename_tac`v NOTIN b`
  \\ `b DELETE v = b` by gs[DELETE_NON_ELEMENT] \\ fs[]
  \\ reverse(Cases_on`CARD v ≤ 4`)
  >- (
    `F` suffices_by rw[]
    \\ pop_assum mp_tac
    \\ simp[]
    \\ qpat_x_assum`_ = 4`(SUBST1_TAC o GSYM)
    \\ simp[]
    \\ Cases_on`PROD_IMAGE CARD b` \\ simp[]
    \\ gs[PROD_IMAGE_EQ_0]
    \\ `count 4 = {}` by metis_tac[empty_partitions]
    \\ fs[])
  \\ cheat
QED
*)

Theorem a_factorisation_of_count_8:
  v1 = {{0;2;4;6};{1;3;5;7}} ∧
  v2 = {{0;1;2;3};{4;5;6;7}} ∧
  v3 = {{0;1;4;7};{2;3;5;6}}
  ⇒
  {v1;v2;v3} factorises count 8
Proof
  strip_tac
  \\ simp[factorises_unique_inter, PULL_EXISTS]
  \\ dsimp[]
  \\ rw[partitions_thm]
  \\ dsimp[EXISTS_UNIQUE_THM]
  \\ EVAL_TAC
QED

Theorem generates_subpartition_SUBSET_cex:
    w = count 8 ∧
    v1 = {{0;2;4;6};{1;3;5;7}} ∧
    v2 = {{0;1;2;3};{4;5;6;7}} ∧
    v3 = {{0;1;4;7};{2;3;5;6}} ∧
    b = {v1;v2;v3} ∧
    c = {v2} ∧
    d = {v1;v2} ∧
    v = {{0;3};{4;5}}
    ⇒
    generates_subpartition w b c v ∧ c ⊆ d ∧ d ⊆ b ∧
    ¬generates_subpartition w b d v
Proof
  strip_tac \\ rpt BasicProvers.VAR_EQ_TAC
  \\ qmatch_goalsub_abbrev_tac`generates_subpartition w b c v`
  \\ qmatch_asmsub_abbrev_tac`b = {v1;v2;v3}`
  \\ qmatch_goalsub_abbrev_tac`c ⊆ d`
  \\ simp[generates_subpartition_common_refinement_refines]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- ( mp_tac a_factorisation_of_count_8 \\ simp[] )
  \\ qabbrev_tac`e = {0;3;4;5}`
  \\ `v partitions e`
  by (
    simp[Abbr`v`, Abbr`e`, partitions_thm, EXISTS_UNIQUE_THM]
    \\ dsimp[PULL_EXISTS] )
  \\ `e ⊆ w` by simp[Abbr`w`, Abbr`e`, SUBSET_DEF]
  \\ conj_asm1_tac >- simp[Abbr`b`,Abbr`c`]
  \\ conj_asm1_tac >- metis_tac[is_subpartition_def]
  \\ `v1 partitions w` by fs[factorises_def, Abbr`b`]
  \\ `v2 partitions w` by fs[factorises_def, Abbr`b`]
  \\ `v3 partitions w` by fs[factorises_def, Abbr`b`]
  \\ `common_refinement w c = v2` by simp[Abbr`c`, common_refinement_SING]
  \\ `subpart_domain w v = e` by metis_tac[subpart_domain_thm]
  \\ simp[]
  \\ qpat_x_assum`_ = v2`kall_tac
  \\ conj_asm1_tac
  >- (
    simp[restrict_partition_def, refines_def, PULL_EXISTS]
    \\ rpt strip_tac
    \\ qexists_tac`if x < 4 then {0;3} else {4;5}`
    \\ simp[Abbr`v`,Abbr`c`]
    \\ `x ∈ count 8` by fs[Abbr`e`]
    \\ `part v2 x ∈ v2` by metis_tac[part_in_partition]
    \\ `x ∈ part v2 x` by metis_tac[in_part]
    \\ rw[Abbr`e`]
    \\ gs[Abbr`v2`, SUBSET_DEF, GSYM DISJOINT_DEF] )
  \\ `c ⊆ d` by simp[Abbr`c`, Abbr`d`]
  \\ `d ⊆ b` by simp[Abbr`b`, Abbr`d`] \\ simp[]
  \\ `∀x. x ∈ e ⇒ chim w b c x x = x`
  by (
    rpt strip_tac
    \\ DEP_REWRITE_TAC[chim_same]
    \\ gs[Abbr`w`, SUBSET_DEF] )
  \\ `part v1 0 = {0; 2; 4; 6} ∧
      part v1 2 = {0; 2; 4; 6} ∧
      part v1 4 = {0; 2; 4; 6} ∧
      part v1 6 = {0; 2; 4; 6} ∧
      part v1 1 = {1; 3; 5; 7} ∧
      part v1 3 = {1; 3; 5; 7} ∧
      part v1 5 = {1; 3; 5; 7} ∧
      part v1 7 = {1; 3; 5; 7} ∧
      part v2 0 = {0; 1; 2; 3} ∧
      part v2 1 = {0; 1; 2; 3} ∧
      part v2 2 = {0; 1; 2; 3} ∧
      part v2 3 = {0; 1; 2; 3} ∧
      part v2 4 = {4; 5; 6; 7} ∧
      part v2 5 = {4; 5; 6; 7} ∧
      part v2 6 = {4; 5; 6; 7} ∧
      part v2 7 = {4; 5; 6; 7} ∧
      part v3 0 = {0; 1; 4; 7} ∧
      part v3 1 = {0; 1; 4; 7} ∧
      part v3 4 = {0; 1; 4; 7} ∧
      part v3 7 = {0; 1; 4; 7} ∧
      part v3 2 = {2; 3; 5; 6} ∧
      part v3 3 = {2; 3; 5; 6} ∧
      part v3 5 = {2; 3; 5; 6} ∧
      part v3 6 = {2; 3; 5; 6}` by (
    rpt conj_tac
    \\ irule EQ_SYM
    \\ irule part_unique
    \\ simp[Abbr`v1`,Abbr`v2`,Abbr`v3`]
    \\ qexists_tac`w`
    \\ simp[] \\ simp[Abbr`w`] )
  \\ `v1 ≠ v2 ∧ v2 ≠ v3 ∧ v3 ≠ v1` by (
    simp[Abbr`v1`,Abbr`v2`,Abbr`v3`]
    \\ EVAL_TAC )
  \\ `chim w b d 3 4 = 1`
  by (
    DEP_REWRITE_TAC[factorises_distinguish]
    \\ drule chim_thm
    \\ disch_then(qspecl_then[`4`,`3`,`d`]mp_tac)
    \\ impl_tac >- simp[Abbr`w`]
    \\ strip_tac
    \\ conj_tac >- (simp[] \\ simp[Abbr`w`])
    \\ simp[]
    \\ simp[Abbr`b`, Abbr`d`, Abbr`c`]
    \\ rpt strip_tac \\ simp[] )
  \\ reverse conj_tac
  >- (
    simp[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ strip_tac
    \\ first_x_assum(qspecl_then[`3`,`4`]mp_tac)
    \\ simp[Abbr`e`] )
  \\ simp[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
  \\ reverse conj_tac
  >- (
    gen_tac \\ strip_tac
    \\ qexistsl_tac[`x`,`x`]
    \\ DEP_REWRITE_TAC[chim_same]
    \\ simp[]
    \\ gs[SUBSET_DEF])
  \\ simp[Abbr`e`]
  \\ qx_genl_tac[`x`,`y`]
  \\ drule chim_thm
  \\ disch_then(qspecl_then[`y`,`x`,`c`]mp_tac)
  \\ strip_tac
  \\ `v1 ∉ c ∧ v2 ∈ c ∧ v3 ∉ c` by simp[Abbr`c`]
  \\ disch_then assume_tac
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac >- fs[Abbr`w`]
  \\ strip_tac
  \\ drule factorises_distinguish
  \\ disch_then(qspec_then`chim w b c x y`mp_tac)
  \\ simp[]
  \\ disch_then(fn th => (
    qspec_then`0`mp_tac th \\
    qspec_then`3`mp_tac th \\
    qspec_then`4`mp_tac th \\
    qspec_then`5`mp_tac th ))
  \\ impl_tac >- simp[Abbr`w`] \\ strip_tac
  \\ impl_tac >- simp[Abbr`w`] \\ strip_tac
  \\ impl_tac >- simp[Abbr`w`] \\ strip_tac
  \\ impl_tac >- simp[Abbr`w`] \\ strip_tac
  \\ simp[]
  \\ ntac 5 (pop_assum kall_tac)
  \\ rw[Abbr`b`, Abbr`c`] \\ dsimp[]
QED

Theorem generates_subpartition_empty:
  generates_subpartition w b c {} ⇔
  b factorises w ∧ c ⊆ b
Proof
  rw[generates_subpartition_def, is_subpartition_empty]
QED

Theorem generates_subpartition_SING:
  generates_subpartition w b c {v} ⇔
  b factorises w ∧ c ⊆ b ∧ v ⊆ w ∧ v ≠ ∅ ∧
  (∀x y. x ∈ v ∧ y ∈ v ⇒ chim w b c x y ∈ v)
Proof
  rw[generates_subpartition_def, is_subpartition_SING]
  \\ rw[EQ_IMP_THM]
  \\ `{v} partitions v` by metis_tac[SING_partitions]
  \\ `subpart_domain w {v} = v`
  by metis_tac[subpart_domain_thm, SUBSET_REFL, is_subpartition_SING]
  >- (
    qpat_x_assum`GSPEC _ = v`(SUBST1_TAC o SYM)
    \\ simp[] \\ metis_tac[] )
  \\ simp[]
  \\ simp[Once SET_EQ_SUBSET]
  \\ reverse conj_tac
  >- (
    simp[SUBSET_DEF]
    \\ rw[]
    \\ qexistsl_tac[`x`,`x`]
    \\ metis_tac[chim_same, SUBSET_DEF] )
  \\ simp[SUBSET_DEF, PULL_EXISTS]
QED

Theorem generates_indiscrete_subpartition:
  generates_subpartition w b c (indiscrete_partition e) ⇔
  b factorises w ∧ c ⊆ b ∧ e ⊆ w ∧
  { chim w b c x y | (x,y) | x ∈ e ∧ y ∈ e } ⊆ e
Proof
  rw[indiscrete_partition_def, generates_subpartition_empty]
  \\ rw[generates_subpartition_SING, SUBSET_DEF, PULL_EXISTS]
QED

Theorem generates_discrete_subpartition:
  generates_subpartition w b c (discrete_partition e)
  ⇔
  b factorises w ∧ c ⊆ b ∧ e ⊆ w ∧
  ∀x y. x ∈ e ∧ y ∈ e ⇒ chim w b c x y = x
Proof
  rw[generates_subpartition_def]
  \\ Cases_on`b factorises w` \\ simp[]
  \\ Cases_on`c ⊆ b` \\ simp[]
  \\ reverse(Cases_on`e ⊆ w`) \\ simp[is_subpartition_discrete]
  >- (
    rw[is_subpartition_def]
    \\ `discrete_partition e partitions e`
    by metis_tac[discrete_partition_partitions]
    \\ disj1_tac
    \\ CCONTR_TAC \\ fs[]
    \\ metis_tac[partitions_inj])
  \\ `subpart_domain w (discrete_partition e) = e` by
  metis_tac[subpart_domain_discrete]
  \\ rw[]
  \\ reverse(rw[EQ_IMP_THM])
  >- (
    rw[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ gs[discrete_partition_def] \\ rw[]
    \\ qexists_tac`x`
    \\ DEP_REWRITE_TAC[chim_same]
    \\ rw[]
    \\ metis_tac[SUBSET_DEF] )
  \\ gs[discrete_partition_def, PULL_EXISTS]
  \\ first_x_assum(qspec_then`x`mp_tac)
  \\ simp[Once SET_EQ_SUBSET]
  \\ simp_tac (std_ss) [SUBSET_DEF]
  \\ rw[PULL_EXISTS]
QED

Theorem DISJOINT_subpart_history_generates_subpartition:
  FINITE b ∧ b factorises w ∧ x partitions e ∧ y partitions e ∧ e ⊆ w ∧
  DISJOINT (subpart_history w b x) (subpart_history w b y)
  ⇒
  generates_subpartition w b (b DIFF subpart_history w b x) y
Proof
  strip_tac
  \\ qmatch_goalsub_abbrev_tac`_ w b nhx y`
  \\ simp[generates_subpartition_common_refinement_refines]
  \\ conj_asm1_tac >- simp[Abbr`nhx`]
  \\ conj_asm1_tac >- metis_tac[is_subpartition_def]
  \\ `is_subpartition w x` by metis_tac[is_subpartition_def]
  \\ qmatch_asmsub_abbrev_tac`DISJOINT hx hy`
  \\ `subpart_domain w y = e` by metis_tac[subpart_domain_thm]
  \\ reverse conj_asm2_tac
  >- (
    simp[Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS]
    \\ reverse conj_tac
    >- (
      qx_gen_tac`s` \\ strip_tac
      \\ qexistsl_tac[`s`,`s`]
      \\ DEP_REWRITE_TAC[chim_same]
      \\ metis_tac[subpart_domain_thm, SUBSET_DEF])
    \\ qx_genl_tac[`p`,`q`] \\ strip_tac
    \\ `chim w b nhx p q = chim w b hx q p`
    by (
      qunabbrev_tac`nhx`
      \\ irule chim_DIFF
      \\ metis_tac[subpart_history_SUBSET_factorisation,
                   SUBSET_DEF] )
    \\ pop_assum SUBST1_TAC
    \\ `generates_subpartition w b hx x` by metis_tac[subpart_history_thm]
    \\ gs[generates_subpartition_subsets, SUBSET_DEF, PULL_EXISTS]
    \\ first_x_assum(qspec_then`part x q`mp_tac)
    \\ impl_keep_tac >- metis_tac[part_in_partition]
    \\ `part x q ⊆ e` by metis_tac[partitions_thm]
    \\ `subpart_domain w x = e` by metis_tac[subpart_domain_thm]
    \\ metis_tac[SUBSET_DEF, in_part] )
  \\ simp[]
  \\ `hy ⊆ nhx`
  by (
    simp[Abbr`nhx`, SUBSET_DEF]
    \\ metis_tac[IN_DISJOINT, subpart_history_SUBSET_factorisation, SUBSET_DEF])
  \\ `common_refinement w nhx refines common_refinement w hy`
  by (
    irule common_refinement_SUBSET
    \\ metis_tac[IN_DIFF, factorises_def])
  \\ irule refines_transitive
  \\ qexists_tac`restrict_partition (common_refinement w hy) e`
  \\ conj_tac
  >- (
    irule imp_restrict_partition_refines
    \\ metis_tac[common_refinement_partitions] )
  \\ `generates_subpartition w b hy y` by metis_tac[subpart_history_thm]
  \\ metis_tac[generates_subpartition_common_refinement_refines]
QED

Theorem subpart_history_restrict:
  FINITE b ∧ b factorises w ∧ x partitions e ∧ y partitions e ∧ e ⊆ w ∧
  DISJOINT (subpart_history w b x) (subpart_history w b y) ∧ z ∈ y
  ⇒
  subpart_history w b (restrict_partition x z) =
  subpart_history w b x
Proof
  strip_tac
  \\ qmatch_asmsub_abbrev_tac`DISJOINT hx hy`
  \\ `generates_subpartition w b (b DIFF hx) y ∧
      generates_subpartition w b (b DIFF hy) x`
  by (
    unabbrev_all_tac
    \\ conj_tac \\ irule DISJOINT_subpart_history_generates_subpartition
    \\ metis_tac[DISJOINT_SYM] )
  \\ `is_subpartition w x ∧ is_subpartition w y ∧
      subpart_domain w x = e ∧ subpart_domain w y = e`
  by metis_tac[subpart_domain_thm, is_subpartition_def]
  \\ simp[SET_EQ_SUBSET]
  \\ conj_asm1_tac
  >- (
    `b DIFF hx ⊆ b` by simp[]
    \\ `{ chim w b (b DIFF hx) s t | s ∈ z ∧ t ∈ e } ⊆ z`
    by metis_tac[generates_subpartition_subsets]
    \\ `{ chim w b hx s t | s ∈ e ∧ t ∈ z } ⊆ z`
    by (
      pop_assum mp_tac
      \\ qmatch_asmsub_abbrev_tac`nhx ⊆ b`
      \\ simp[SUBSET_DEF, PULL_EXISTS]
      \\ rpt strip_tac
      \\ first_x_assum(qspecl_then[`t`,`s`]mp_tac)
      \\ impl_tac >- simp[]
      \\ qunabbrev_tac`nhx`
      \\ DEP_REWRITE_TAC[chim_DIFF]
      \\ metis_tac[SUBSET_DEF, partitions_thm,
                   subpart_history_SUBSET_factorisation] )
    \\ `∀p. p ∈ x ⇒ { chim w b hx s t | s ∈ p INTER z ∧ t ∈ z } ⊆ z`
    by (
      fs[SUBSET_DEF, PULL_EXISTS]
      \\ rpt strip_tac
      \\ first_x_assum irule
      \\ metis_tac[partitions_thm, SUBSET_DEF])
    \\ `∀p. p ∈ x ⇒ { chim w b hx s t | s ∈ p INTER z ∧ t ∈ z } ⊆ p INTER z`
    by (
      fs[SUBSET_DEF, PULL_EXISTS]
      \\ gen_tac \\ strip_tac
      \\ reverse conj_tac >- metis_tac[]
      \\ rpt strip_tac
      \\ `generates_subpartition w b hx x` by metis_tac[subpart_history_thm]
      \\ pop_assum mp_tac
      \\ simp[generates_subpartition_subsets, SUBSET_DEF, PULL_EXISTS]
      \\ rpt strip_tac
      \\ first_x_assum irule
      \\ metis_tac[partitions_thm, SUBSET_DEF])
    \\ irule imp_subpart_history_SUBSET
    \\ `z ⊆ e` by metis_tac[partitions_thm, SUBSET_DEF]
    \\ rpt(conj_tac >- simp[])
    \\ `restrict_partition x z partitions z`
    by metis_tac[restrict_partition_partitions]
    \\ conj_asm1_tac >- metis_tac[is_subpartition_def, SUBSET_TRANS]
    \\ simp[generates_subpartition_subsets]
    \\ conj_asm1_tac >- metis_tac[subpart_history_SUBSET_factorisation]
    \\ `subpart_domain w (restrict_partition x z) = z`
    by metis_tac[subpart_domain_thm, SUBSET_TRANS]
    \\ simp[restrict_partition_def, PULL_EXISTS]
    \\ qx_gen_tac`p` \\ strip_tac
    \\ `part x p ∈ x` by metis_tac[part_in_partition, SUBSET_DEF]
    \\ first_x_assum drule \\ simp[]
    \\ first_x_assum drule \\ simp[])
  \\ qunabbrev_tac`hx`
  \\ irule imp_subpart_history_SUBSET
  \\ qmatch_asmsub_abbrev_tac`DISJOINT hx hy`
  \\ simp[]
  \\ simp[generates_subpartition_in_parts]
  \\ `z ⊆ e` by metis_tac[partitions_thm, SUBSET_DEF]
  \\ `restrict_partition x z partitions z`
  by metis_tac[restrict_partition_partitions]
  \\ `is_subpartition w (restrict_partition x z)`
  by metis_tac[is_subpartition_def, SUBSET_TRANS]
  \\ `subpart_domain w (restrict_partition x z) = z`
  by metis_tac[subpart_domain_thm, SUBSET_TRANS]
  \\ conj_asm1_tac >- metis_tac[subpart_history_SUBSET_factorisation]
  \\ qx_genl_tac[`s`,`t`] \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`subpart_history _ _ rx`
  \\ `hx ⊆ b DIFF hy`
  by metis_tac[SUBSET_DEF, IN_DISJOINT, IN_DIFF, subpart_history_thm]
  \\ `subpart_history w b rx = (b DIFF hy) ∩ subpart_history w b rx`
  by metis_tac[SUBSET_INTER2, SUBSET_TRANS]
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[chim_INTER]
  \\ conj_tac
  >- metis_tac[SUBSET_DEF, IN_DIFF, subpart_history_SUBSET_factorisation]
  \\ qmatch_goalsub_abbrev_tac`chim w b hrx s t`
  \\ `z <> {}` by metis_tac[partitions_thm]
  \\ `∃r. r ∈ z` by metis_tac[MEMBER_NOT_EMPTY]
  \\ `generates_subpartition w b hy y` by metis_tac[subpart_history_thm]
  \\ `{chim w b hy x y | (x, y) | x ∈ z ∧ y ∈ e } = z`
  by metis_tac[generates_subpartition_def]
  \\ `chim w b hy r t ∈ z ∧ chim w b hy r s ∈ z`
  by (
    pop_assum mp_tac
    \\ simp[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS] )
  \\ `generates_subpartition w b hrx rx` by metis_tac[subpart_history_thm]
  \\ qabbrev_tac`s' = chim w b hrx (chim w b hy r s) (chim w b hy r t)`
  \\ `s' ∈ part rx (chim w b hy r s)`
  by (
    qunabbrev_tac`s'` \\ pop_assum mp_tac
    \\ simp[generates_subpartition_in_parts]
    \\ metis_tac[] )
  \\ `chim w b hy r s = chim w b (b DIFF hy) s r`
  by (
    DEP_REWRITE_TAC[chim_DIFF]
    \\ simp[]
    \\ metis_tac[subpart_history_SUBSET_factorisation, SUBSET_DEF])
  \\ `r ∈ e` by fs[SUBSET_DEF]
  \\ `chim w b hy r s ∈ part x s`
  by metis_tac[generates_subpartition_in_parts]
  \\ `part x (chim w b hy r s) = part x s`
  by (
    irule EQ_SYM
    \\ irule part_unique
    \\ conj_tac >- simp[]
    \\ conj_tac >- metis_tac[part_in_partition]
    \\ metis_tac[SUBSET_DEF])
  \\ `s' ∈ part x s`
  by (
    `part rx (chim w b hy r s) ⊆ part x (chim w b hy r s)`
    suffices_by metis_tac[SUBSET_DEF]
    \\ qunabbrev_tac`rx`
    \\ DEP_REWRITE_TAC[Q.GEN`w`part_restrict_partition]
    \\ simp[]
    \\ metis_tac[])
  \\ `part x s = part x s'` by (
    irule part_unique
    \\ simp[]
    \\ conj_asm1_tac
    >- (
      irule part_in_partition
      \\ metis_tac[] )
    \\ goal_assum(last_assum o mp_then Any mp_tac)
    \\ metis_tac[partitions_thm, SUBSET_DEF] )
  \\ `chim w b (b DIFF hy) (chim w b hrx s t) t = chim w b (b DIFF hy) s' t`
  suffices_by (
    disch_then SUBST1_TAC
    \\ pop_assum SUBST_ALL_TAC
    \\ `part x s' ∈ x` by metis_tac[part_in_partition, SUBSET_DEF]
    \\ `{ chim w b (b DIFF hy) a y |(a,y) | a ∈ part x s' ∧ y ∈ e } = part x s'`
    by metis_tac[generates_subpartition_def]
    \\ pop_assum mp_tac \\ simp[SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS])
  \\ `s' = chim w b hy r (chim w b hrx s t)`
  by (
    qunabbrev_tac`s'`
    \\ `r ∈ w ∧ s ∈ w ∧ t ∈ w` by metis_tac[SUBSET_DEF]
    \\ metis_tac[chim_compose] )
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[chim_DIFF]
  \\ conj_tac
  >- (
    `s ∈ w ∧ t ∈ w ∧ r ∈ w` by metis_tac[SUBSET_DEF]
    \\ conj_asm1_tac >- metis_tac[chim_thm]
    \\ conj_tac >- simp[]
    \\ conj_asm1_tac >- metis_tac[subpart_history_SUBSET_factorisation]
    \\ conj_tac >- metis_tac[chim_thm]
    \\ rw[])
  \\ `s ∈ w ∧ t ∈ w ∧ r ∈ w` by metis_tac[SUBSET_DEF]
  \\ `chim w b hrx s t ∈ w` by metis_tac[chim_thm]
  \\ metis_tac[chim_squeeze]
QED

Theorem chim_BIGUNION_SUBSET:
  b factorises w ∧ e ⊆ w ⇒
  !sos. FINITE sos ==>
    (!c. c IN sos ==> c ⊆ b ∧ (!s t. s IN e /\ t IN e ==> chim w b c s t ∈ e))
    ==>
    !s t. s IN e /\ t IN e ==> chim w b (BIGUNION sos) s t ∈ e
Proof
  strip_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rewrite_tac[BIGUNION_EMPTY]
  \\ conj_tac
  >- (
    rpt strip_tac
    \\ DEP_REWRITE_TAC[chim_empty]
    \\ fs[SUBSET_DEF])
  \\ ntac 2 strip_tac
  \\ qx_gen_tac`z` \\ strip_tac \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`chim w b bs _ _ ∈ e`
  \\ rewrite_tac[BIGUNION_INSERT]
  \\ rpt strip_tac
  \\ DEP_REWRITE_TAC[chim_UNION]
  \\ conj_tac >- (
    simp[Abbr`bs`]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[])
  \\ asm_simp_tac std_ss []
  \\ fs[]
QED

Theorem subpart_history_common_refinement_SUBSET_BIGUNION:
  FINITE b ∧ b factorises w ∧ e ⊆ w ∧
  (!v. v IN sop ==> is_subpartition w v ∧ subpart_domain w v = e) ==>
    subpart_history w b (common_refinement e sop) ⊆
    BIGUNION (IMAGE (subpart_history w b) sop)
Proof
  rpt strip_tac
  \\ irule imp_subpart_history_SUBSET
  \\ simp[is_subpartition_common_refinement]
  \\ qmatch_goalsub_abbrev_tac`generates_subpartition _ _ bu`
  \\ simp[generates_subpartition_common_refinement_refines]
  \\ conj_asm1_tac
  >- (
    simp[SUBSET_DEF, PULL_EXISTS, Abbr`bu`]
    \\ rw[]
    \\ res_tac
    \\ imp_res_tac subpart_history_SUBSET_factorisation
    \\ fs[SUBSET_DEF])
  \\ conj_asm1_tac >- simp[is_subpartition_common_refinement]
  \\ `common_refinement e sop partitions e` by simp[common_refinement_partitions]
  \\ `subpart_domain w (common_refinement e sop) = e`
  by metis_tac[subpart_domain_thm]
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    irule refines_common_refinement
    \\ reverse conj_tac
    >- metis_tac[restrict_partition_partitions, common_refinement_partitions]
    \\ gen_tac \\ strip_tac
    \\ conj_asm1_tac >- metis_tac[subpart_domain_thm]
    \\ irule refines_transitive
    \\ qexists_tac`common_refinement e
                     (IMAGE (λv. restrict_partition v e) (subpart_history w b x))`
    \\ conj_tac
    >- (
      DEP_ONCE_REWRITE_TAC[restrict_partition_common_refinement]
      \\ conj_asm1_tac
      >- (
        simp[Abbr`bu`, PULL_EXISTS]
        \\ rw[]
        \\ drule subpart_history_SUBSET_factorisation
        \\ disch_then drule
        \\ qmatch_assum_rename_tac`v ∈ subpart_history w b z`
        \\ disch_then(qspec_then`z`mp_tac)
        \\ impl_tac >- metis_tac[]
        \\ simp[SUBSET_DEF]
        \\ disch_then drule
        \\ fs[factorises_def])
      \\ irule common_refinement_SUBSET
      \\ simp[PULL_EXISTS]
      \\ conj_asm1_tac >- metis_tac[restrict_partition_partitions]
      \\ simp[SUBSET_DEF, PULL_EXISTS, Abbr`bu`]
      \\ metis_tac[])
    \\ DEP_REWRITE_TAC[GSYM restrict_partition_common_refinement]
    \\ conj_asm1_tac
    >- (
      rw[]
      \\ drule subpart_history_SUBSET_factorisation
      \\ disch_then drule
      \\ disch_then(qspec_then`x`mp_tac)
      \\ impl_tac >- metis_tac[]
      \\ simp[SUBSET_DEF]
      \\ fs[factorises_def])
    \\ `generates_subpartition w b (subpart_history w b x) x`
    by metis_tac[subpart_history_thm]
    \\ fs[generates_subpartition_common_refinement_refines]
    \\ `subpart_domain w x = e` by metis_tac[] \\ fs[])
  \\ simp[SET_EQ_SUBSET]
  \\ reverse conj_tac
  >- (
    simp[SUBSET_DEF]
    \\ rpt strip_tac
    \\ qexistsl_tac[`x`,`x`]
    \\ DEP_REWRITE_TAC[chim_same]
    \\ simp[] \\ fs[SUBSET_DEF] )
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qx_genl_tac[`s`,`t`] \\ strip_tac
  \\ `FINITE bu` by metis_tac[SUBSET_FINITE]
  \\ qmatch_asmsub_abbrev_tac`BIGUNION sos`
  \\ `FINITE sos` by metis_tac[FINITE_BIGUNION_EQ]
  \\ qunabbrev_tac`bu`
  \\ irule chim_BIGUNION_SUBSET
  \\ rw[Abbr`sos`]
  >- (
    irule subpart_history_SUBSET_factorisation
    \\ metis_tac[])
  \\ `generates_subpartition w b (subpart_history w b x) x`
  by metis_tac[subpart_history_thm]
  \\ fs[generates_subpartition_common_refinement_refines]
  \\ `subpart_domain w x = e` by metis_tac[] \\ fs[]
  \\ fs[SUBSET_DEF, PULL_EXISTS, SET_EQ_SUBSET]
QED

Theorem subpart_history_common_refinement_BIGUNION:
  FINITE b ∧ b factorises w ∧ e ⊆ w ∧
  (!v. v IN sop ==> is_subpartition w v ∧ subpart_domain w v = e) ==>
    subpart_history w b (common_refinement e sop) =
    BIGUNION (IMAGE (subpart_history w b) sop)
Proof
  rpt strip_tac
  \\ rewrite_tac[SET_EQ_SUBSET]
  \\ drule subpart_history_common_refinement_SUBSET_BIGUNION
  \\ disch_then (first_assum o mp_then (Pat`(factorises)`) mp_tac)
  \\ rpt(disch_then drule)
  \\ first_assum(mp_then(Pat`(factorises)`)mp_tac
                   subpart_history_common_refinement_BIGUNION_SUBSET)
  \\ rpt(disch_then drule)
  \\ rw[]
QED

Triviality subpart_history_binary_refinement_2:
  FINITE b ∧ b factorises w ∧ x partitions e ∧ y partitions e ∧ e ⊆ w ∧
  FINITE x ∧ CARD x = 2 ⇒
  subpart_history w b (common_refinement e {x; y}) ⊆
  subpart_history w b x ∪
    BIGUNION (IMAGE (λz. subpart_history w b (restrict_partition y z)) x)
Proof
  strip_tac
  \\ Cases_on`x` \\ gs[]
  \\ Cases_on`t` \\ gs[]
  \\ BasicProvers.VAR_EQ_TAC
  \\ qmatch_asmsub_rename_tac`{x1; x2}`
  \\ irule imp_subpart_history_SUBSET
  \\ conj_tac >- simp[]
  \\ conj_tac >- simp[]
  \\ conj_asm1_tac >- simp[is_subpartition_common_refinement]
  \\ rewrite_tac[generates_subpartition_subsets_parts]
  \\ conj_tac >- simp[]
  \\ conj_asm1_tac >- (
    simp[] \\ rpt conj_tac \\ irule subpart_history_SUBSET_factorisation
    \\ rw[is_subpartition_def]
    \\ `x1 ⊆ e ∧ x2 ⊆ e` by (fs[partitions_thm] \\ metis_tac[])
    \\ metis_tac[restrict_partition_partitions, SUBSET_TRANS])
  \\ conj_tac >- simp[]
  \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
  \\ conj_tac >- dsimp[]
  \\ qmatch_goalsub_abbrev_tac`chim w b cc _ _`
  \\ simp[PULL_EXISTS]
  \\ qx_genl_tac[`s`,`t`] \\ strip_tac
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[GSYM FORALL_AND_THM]
  \\ qx_genl_tac[`u`,`v`]
  \\ Cases_on`u ∈ e ∧ v ∈ e` \\ gs[]
  \\ Cases_on`u ∈ part {x1; x2} s ∧ u ∈ part y s ∧ v ∈ part y t` \\ gs[]
  \\ Cases_on`v ∈ part {x1; x2} t` \\ gs[]
  \\ `∃r. r ∈ e ∧ r ∉ part {x1; x2} s`
  by (
    qpat_assum`_ _ partitions e`mp_tac
    \\ simp_tac (srw_ss()) [partitions_thm]
    \\ strip_tac
    \\ qexists_tac`CHOICE (if part {x1; x2} s = x1 then x2 else x1)`
    \\ conj_asm1_tac >- metis_tac[CHOICE_DEF, SUBSET_DEF]
    \\ `x1 ∈ {x1; x2} ∧ x2 ∈ {x1; x2}` by simp[]
    \\ `part {x1; x2} s ∈ {x1; x2}` by metis_tac[part_in_partition]
    \\ pop_assum mp_tac \\ simp[]
    \\ metis_tac[partitions_DISJOINT, IN_DISJOINT, CHOICE_DEF])
  \\ qabbrev_tac`cg = λx.
       subpart_history w b (restrict_partition y (part {x1; x2} x))`
  \\ qabbrev_tac`c = subpart_history w b {x1; x2}`
  \\ `cc = cg s  ∪ (c ∪ cg r)` by (
    gs[Abbr`cg`]
    \\ `part {x1; x2} s ∈ {x1; x2} ∧ part {x1; x2} r ∈ {x1; x2}`
    by metis_tac[part_in_partition]
    \\ `s ∈ part {x1; x2} s ∧ r ∈ part {x1; x2} r`
    by metis_tac[in_part]
    \\ gs[]
    \\ metis_tac[UNION_ASSOC, UNION_COMM])
  \\ `chim w b cc u v = chim w b (cg s) u (chim w b c u (chim w b (cg r) u v))`
  by (
    pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[chim_UNION]
    \\ fs[Abbr`cc`, SUBSET_DEF, Abbr`cg`]
    \\ `part {x1; x2} s ∈ {x1; x2} ∧ part {x1; x2} r ∈ {x1; x2}`
    by metis_tac[part_in_partition]
    \\ fs[])
  \\ `part y s ⊆ e` by metis_tac[partitions_thm, part_in_partition]
  \\ conj_asm2_tac >- metis_tac[SUBSET_DEF]
  \\ `chim w b c u (chim w b (cg r) u v) =
      chim w b c u (chim w b c r (chim w b (cg r) u v))`
  by (
    irule (chim_squeeze |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GSYM)
    \\ metis_tac[chim_thm, SUBSET_DEF])
  \\ `chim w b c r (chim w b (cg r) u v) =
      chim w b (cg r) (chim w b c r u) (chim w b c r v)`
  by (
    irule (chim_compose |> UNDISCH |> CONJUNCT1 |> DISCH_ALL)
    \\ metis_tac[SUBSET_DEF])
  \\ `generates_subpartition w b c {x1; x2}`
  by metis_tac[subpart_history_thm, is_subpartition_def]
  \\ `subpart_domain w {x1; x2} = e`
  by metis_tac[subpart_domain_thm, is_subpartition_def]
  \\ `chim w b c r u ∈ part {x1; x2} r ∧
      chim w b c r v ∈ part {x1; x2} r`
  by metis_tac[generates_subpartition_in_parts]
  \\ qabbrev_tac`xr = part {x1; x2} r`
  \\ `xr ⊆ e` by (
    `xr ∈ {x1; x2}` by metis_tac[part_in_partition]
    \\ fs[partitions_thm] )
  \\ `is_subpartition e (restrict_partition y xr)`
  by metis_tac[is_subpartition_restrict]
  \\ qmatch_asmsub_abbrev_tac`is_subpartition e rxr`
  \\ `is_subpartition w rxr` by metis_tac[is_subpartition_def, SUBSET_TRANS]
  \\ `generates_subpartition w b (cg r) rxr` by metis_tac[subpart_history_thm]
  \\ `part {x1; x2} (chim w b c r u) = xr`
  by (
    qunabbrev_tac`xr`
    \\ irule EQ_SYM
    \\ irule part_unique
    \\ metis_tac[part_in_partition, SUBSET_DEF])
  \\ `subpart_domain e rxr = xr` by metis_tac[subpart_domain_restrict]
  \\ `subpart_domain w rxr = xr` by metis_tac[subpart_domain_thm, SUBSET_TRANS]
  \\ `chim w b c r (chim w b (cg r) u v) ∈ part rxr (chim w b c r u)`
  by metis_tac[generates_subpartition_in_parts]
  \\ `part rxr (chim w b c r u) ∈ rxr`
  by metis_tac[part_in_partition, subpart_domain_thm, SUBSET_DEF]
  \\ `part rxr (chim w b c r u) ⊆ xr` by (
    fs[restrict_partition_def, Abbr`rxr`] )
  \\ `chim w b c r (chim w b (cg r) u v) ∈ xr` by metis_tac[SUBSET_DEF]
  \\ qmatch_goalsub_abbrev_tac`cuv ∈ _`
  \\ qpat_x_assum`cuv = _`SUBST_ALL_TAC
  \\ qmatch_goalsub_abbrev_tac`chim w b _ u cuuv`
  \\ qpat_x_assum`cuuv = _`SUBST_ALL_TAC
  \\ qmatch_goalsub_abbrev_tac`chim w b c u cruv`
  \\ qpat_x_assum`cruv = _`SUBST_ALL_TAC
  \\ qmatch_goalsub_abbrev_tac`chim w b c u crruv`
  \\ qabbrev_tac`xs = part {x1; x2} s`
  \\ `xs ⊆ e` by (
    `xs ∈ {x1; x2}` by metis_tac[part_in_partition]
    \\ fs[partitions_thm] )
  \\ `is_subpartition e (restrict_partition y xs)`
  by metis_tac[is_subpartition_restrict]
  \\ qmatch_asmsub_abbrev_tac`is_subpartition e rxs`
  \\ `is_subpartition w rxs` by metis_tac[is_subpartition_def, SUBSET_TRANS]
  \\ `generates_subpartition w b (cg s) rxs` by metis_tac[subpart_history_thm]
  \\ `crruv ∈ e` by metis_tac[SUBSET_DEF]
  \\ `part {x1; x2} u = xs`
  by (
    qunabbrev_tac`xs`
    \\ irule EQ_SYM
    \\ irule part_unique
    \\ metis_tac[part_in_partition])
  \\ `chim w b c u crruv ∈ xs`
  by metis_tac[generates_subpartition_in_parts]
  \\ `subpart_domain e rxs = xs` by metis_tac[subpart_domain_restrict]
  \\ `subpart_domain w rxs = xs` by metis_tac[subpart_domain_thm, SUBSET_TRANS]
  \\ `part rxs u ∈ rxs`
  by metis_tac[part_in_partition, subpart_domain_thm, SUBSET_DEF]
  \\ `part rxs u ⊆ xs`
  by fs[restrict_partition_def, Abbr`rxs`]
  \\ `chim w b (cg s) u (chim w b c u crruv) ∈ part rxs u`
  by metis_tac[generates_subpartition_in_parts]
  \\ conj_asm1_tac >- metis_tac[SUBSET_DEF]
  \\ `part rxs u ⊆ part y s`
  by (
    qunabbrev_tac`rxs`
    \\ DEP_REWRITE_TAC[Q.GEN`w`part_restrict_partition]
    \\ conj_tac >- metis_tac[]
    \\ `part y u = part y s` suffices_by metis_tac[INTER_SUBSET]
    \\ irule EQ_SYM
    \\ irule part_unique
    \\ metis_tac[part_in_partition])
  \\ metis_tac[SUBSET_DEF]
QED

Theorem subpart_history_binary_refinement_restrict:
  FINITE b ∧ b factorises w ∧ x partitions e ∧ y partitions e ∧ e ⊆ w ⇒
  subpart_history w b (common_refinement e {x; y}) =
  subpart_history w b x ∪
    BIGUNION (IMAGE (λz. subpart_history w b (restrict_partition y z)) x)
Proof
  strip_tac
  \\ `common_refinement e {x; y} refines x`
  by (
    irule common_refinement_refines
    \\ rw[] \\ rw[] )
  \\ first_assum (mp_then Any mp_tac refines_subpart_history)
  \\ disch_then drule \\ disch_then drule
  \\ impl_keep_tac
  >- (
    conj_asm1_tac
    >- metis_tac[is_subpartition_common_refinement]
    \\ conj_asm1_tac >- metis_tac[is_subpartition_def]
    \\ metis_tac[is_subpartition_common_refinement, subpart_domain_thm])
  \\ strip_tac
  \\ simp[Once SET_EQ_SUBSET]
  \\ reverse conj_tac
  >- (
    simp[BIGUNION_SUBSET, PULL_EXISTS]
    \\ rpt strip_tac
    \\ irule SUBSET_subpart_history
    \\ gs[]
    \\ reverse conj_tac
    >- (
      simp[is_subpartition_def]
      \\ metis_tac[restrict_partition_partitions, SUBSET_TRANS, partitions_thm])
    \\ simp[SUBSET_DEF]
    \\ simp[restrict_partition_def, PULL_EXISTS]
    \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
    \\ dsimp[]
    \\ qx_gen_tac`a` \\ strip_tac
    \\ `z ⊆ e` by metis_tac[partitions_thm]
    \\ qexists_tac`a`
    \\ `a ∈ e` by metis_tac[SUBSET_DEF]
    \\ simp[]
    \\ simp[Once SET_EQ_SUBSET]
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_asm1_tac >- metis_tac[SUBSET_INTER_SUBSET, INTER_COMM]
    \\ `part y a ∈ y ∧ part x a ∈ x` by metis_tac[part_in_partition]
    \\ `part y a ⊆ e ∧ part x a ⊆ e` by metis_tac[partitions_thm]
    \\ `z = part x a` by metis_tac[part_unique]
    \\ BasicProvers.VAR_EQ_TAC
    \\ metis_tac[INTER_SUBSET, INTER_COMM, INTER_ASSOC])
  \\ Cases_on`x = {}`
  >- gs[common_refinement_def, partition_on_empty]
  \\ Cases_on`SING x`
  >- (
    `x = {e} ∧ e ≠ ∅` by metis_tac[SING_partitions, SING_DEF, EQUAL_SING]
    \\ `common_refinement e {x; y} = y`
    by (
      DEP_REWRITE_TAC[common_refinement_BIGINTER]
      \\ conj_tac >- (gs[] \\ dsimp[])
      \\ simp[Once SET_EQ_SUBSET]
      \\ simp[SUBSET_DEF, PULL_EXISTS, part_SING]
      \\ conj_tac
      >- (
        qx_gen_tac`z`
        \\ strip_tac
        \\ `part y z ∈ y` by metis_tac[part_in_partition]
        \\ `part y z ⊆ e` by metis_tac[partitions_thm]
        \\ metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM] )
      \\ qx_gen_tac`z` \\ strip_tac
      \\ qexists_tac`CHOICE z`
      \\ `z ⊆ e ∧ z ≠ ∅` by metis_tac[partitions_thm]
      \\ `CHOICE z ∈ z` by metis_tac[CHOICE_DEF]
      \\ `CHOICE z ∈ e` by metis_tac[SUBSET_DEF]
      \\ `part y (CHOICE z) ⊆ e` by metis_tac[part_in_partition, partitions_thm]
      \\ simp[part_SING]
      \\ `z = part y (CHOICE z)` by metis_tac[part_unique]
      \\ metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM])
    \\ gs[trivial_restrict_partition] )
  \\ Cases_on`FINITE x ∧ CARD x = 2`
  >- (
    drule subpart_history_binary_refinement_2
    \\ disch_then drule \\ fs[] )
  \\ qmatch_goalsub_abbrev_tac`subpart_history w b cr`
  \\ `∀s. s ∈ x ⇒ s PSUBSET e`
  by (
    simp[PSUBSET_DEF]
    \\ gen_tac \\ strip_tac
    \\ conj_asm1_tac >- metis_tac[partitions_thm]
    \\ strip_tac \\ rw[]
    \\ `∃v. v ∈ x ∧ v ≠ e`
    by (
      CCONTR_TAC
      \\ fs[SING_DEF]
      \\ qpat_x_assum`∀z. x <> _`mp_tac
      \\ simp[]
      \\ qexists_tac`e`
      \\ simp[Once EXTENSION]
      \\ metis_tac[])
    \\ `DISJOINT e v` by metis_tac[partitions_DISJOINT]
    \\ `v ⊆ e ∧ v ≠ {}` by metis_tac[partitions_thm]
    \\ metis_tac[SUBSET_DEF, IN_DISJOINT, MEMBER_NOT_EMPTY] )
  \\ `cr = common_refinement e
       (IMAGE (λx. (e DIFF x) INSERT restrict_partition y x) x)`
  by (
    simp[Abbr`cr`]
    \\ qmatch_goalsub_abbrev_tac`_ = _ _ (IMAGE vf _)`
    \\ `∀a. a ∈ x ⇒ vf a partitions e`
    by (
      rw[Abbr`vf`]
      \\ irule pull_out_partition
      \\ simp[] )
    \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
    \\ simp[GSYM CONJ_ASSOC]
    \\ conj_tac >- dsimp[]
    \\ conj_tac >- simp[PULL_EXISTS]
    \\ irule IMAGE_CONG \\ simp[]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ simp[Once EXTENSION, PULL_EXISTS]
    \\ qx_gen_tac`a`
    \\ Cases_on`a ∈ e` \\ simp[]
    \\ eq_tac \\ strip_tac
    >- (
      qx_gen_tac`c` \\ strip_tac
      \\ `part (vf c) z ∈ vf c` by metis_tac[part_in_partition]
      \\ `z ∈ part (vf c) z` by metis_tac[in_part]
      \\ gs[Abbr`vf`]
      >- (
        strip_tac
        \\ `c = part x a` by metis_tac[part_unique]
        \\ `a ∈ part x a` by metis_tac[in_part]
        \\ `part x z = part x a` by metis_tac[part_unique, part_in_partition]
        \\ gs[]
        \\ metis_tac[in_part])
      \\ gs[restrict_partition_def]
      \\ qmatch_asmsub_rename_tac`z ∈ part y q`
      \\ `c ⊆ e` by metis_tac[partitions_thm]
      \\ `z ∈ part y z` by metis_tac[in_part]
      \\ `part y q ∈ y ∧ part y z ∈ y`
      by metis_tac[part_in_partition, SUBSET_DEF]
      \\ `part y q = part y z` by metis_tac[part_unique] \\ gs[]
      \\ `part x z = part x a` by metis_tac[part_unique]
      \\ `part x z = c` by metis_tac[part_unique]
      \\ gs[])
    \\ `part x a ∈ x` by metis_tac[part_in_partition]
    \\ `a ∈ part (vf (part x a)) z` by metis_tac[]
    \\ `part (vf (part x a)) z ∈ vf (part x a)` by metis_tac[part_in_partition]
    \\ `a ∈ part x a` by metis_tac[in_part]
    \\ `z ∈ part (vf (part x a)) z` by metis_tac[in_part]
    \\ fs[Abbr`vf`, restrict_partition_def] \\ fs[]
    \\ rfs[]
    \\ qmatch_asmsub_rename_tac`a ∈ part y q`
    \\ `q ∈ e` by metis_tac[partitions_thm, SUBSET_DEF]
    \\ `part y q ∈ y` by metis_tac[part_in_partition]
    \\ `part y q = part y z` by metis_tac[part_unique] \\ gs[]
    \\ `part x a = part x z` by metis_tac[part_unique]
    \\ gs[])
  \\ first_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[subpart_history_common_refinement_BIGUNION]
  \\ conj_asm1_tac
  >- (
    simp[PULL_EXISTS] \\ qx_gen_tac`z` \\ strip_tac
    \\ drule pull_out_partition
    \\ disch_then(qspec_then`z`mp_tac)
    \\ metis_tac[subpart_domain_thm, is_subpartition_def])
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qx_gen_tac`v`
  \\ qx_gen_tac`s`
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`v ∈ _ _ _ u`
  \\ `u partitions e` by metis_tac[pull_out_partition]
  \\ `{e DIFF s; s} partitions e`
  by metis_tac[INSERT_COMM, binary_partition, partitions_thm]
  \\ `u = common_refinement e {{e DIFF s; s}; u}`
  by (
    DEP_REWRITE_TAC[common_refinement_BIGINTER]
    \\ dsimp[]
    \\ simp[Abbr`u`]
    \\ simp[Once EXTENSION]
    \\ qx_gen_tac`z`
    \\ rw[EQ_IMP_THM]
    >- (
      qexists_tac`CHOICE (e DIFF s)`
      \\ `e DIFF s <> {}`
      by metis_tac[PSUBSET_DEF, SUBSET_DIFF_EMPTY, SET_EQ_SUBSET]
      \\ drule CHOICE_DEF
      \\ simp[] \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`part bv c ∩ part rv _`
      \\ `part bv c ∈ bv ∧ part rv c ∈ rv` by metis_tac[part_in_partition]
      \\ `c ∈ part bv c ∧ c ∈ part rv c` by metis_tac[in_part]
      \\ ntac 4 (pop_assum mp_tac)
      \\ rw[Abbr`bv`,Abbr`rv`] \\ gs[]
      >- ( simp[Once EXTENSION] \\ metis_tac[] )
      \\ gs[restrict_partition_def])
    >- (
      qexists_tac`CHOICE z`
      \\ `z <> {}` by metis_tac[partitions_thm, restrict_partition_partitions]
      \\ drule CHOICE_DEF \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac`part bv c ∩ part rv _`
      \\ `z ⊆ e ∧ z ⊆ s`
      by (
        fs[restrict_partition_def, SUBSET_DEF, PSUBSET_DEF]
        \\ metis_tac[])
      \\ `part bv c ∈ bv ∧ part rv c ∈ rv`
      by metis_tac[part_in_partition, SUBSET_DEF]
      \\ `c ∈ part bv c ∧ c ∈ part rv c` by metis_tac[in_part, SUBSET_DEF]
      \\ gs[Abbr`bv`, Abbr`rv`, SUBSET_DEF]
      \\ qmatch_asmsub_abbrev_tac`c ∈ part rv c`
      \\ `z = part rv c` by (
        irule part_unique
        \\ `z ∈ rv` by simp[Abbr`rv`]
        \\ metis_tac[])
      \\ simp[Once EXTENSION]
      \\ metis_tac[])
    >- (
      qmatch_goalsub_abbrev_tac`part bv c ∩ part rv _`
      \\ `part rv c ∈ rv` by metis_tac[part_in_partition]
      \\ `part bv c ∈ bv` by metis_tac[part_in_partition]
      \\ `part bv c ⊆ e ∧ part rv c ⊆ e` by metis_tac[partitions_thm]
      \\ `c ∈ part bv c ∧ c ∈ part rv c` by metis_tac[in_part]
      \\ `∀v. v <> e DIFF s /\ v ∈ restrict_partition y s ⇒ DISJOINT v (e DIFF s)`
      by metis_tac[IN_INSERT, partitions_DISJOINT]
      \\ Cases_on`part bv c = e DIFF s`
      >- (
        `c ∉ s` by metis_tac[IN_DIFF]
        \\ reverse(Cases_on`part rv c = e DIFF s`)
        >- (
          `part rv c ∈ restrict_partition y s` by fs[Abbr`rv`]
          \\ metis_tac[IN_DISJOINT] )
        \\ simp[]
        \\ disj1_tac
        \\ simp[Once EXTENSION]
        \\ metis_tac[] )
      \\ `part bv c = s` by fs[Abbr`bv`]
      \\ Cases_on`part rv c = e DIFF s`
      >- metis_tac[IN_DIFF]
      \\ `part rv c ∈ restrict_partition y s` by fs[Abbr`rv`]
      \\ disj2_tac
      \\ pop_assum mp_tac
      \\ simp[restrict_partition_def, PULL_EXISTS]
      \\ rpt strip_tac
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[Once EXTENSION]
      \\ `∀x. x ∈ s ==> x ∈ e` by metis_tac[PSUBSET_DEF, SUBSET_DEF]
      \\ metis_tac[]))
  \\ drule subpart_history_binary_refinement_2
  \\ disch_then drule
  \\ disch_then(qspecl_then[`u`,`{e DIFF s; s}`]mp_tac)
  \\ disch_then drule
  \\ impl_tac >- (
    rw[]
    \\ `s = {}` by metis_tac[MEMBER_NOT_EMPTY, IN_DIFF, EXTENSION]
    \\ metis_tac[partitions_thm])
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ disch_then drule
  \\ `e DIFF s <> {}`
  by metis_tac[MEMBER_NOT_EMPTY, IN_DIFF, EXTENSION, PSUBSET_DEF, SUBSET_DEF]
  \\ `x refines {e DIFF s; s}`
  by (
    dsimp[refines_def]
    \\ rw[]
    \\ Cases_on`s1 ⊆ s` \\ rw[]
    \\ `s1 ⊆ e` by metis_tac[partitions_thm]
    \\ fs[SUBSET_DEF] \\ rw[]
    \\ Cases_on`s1 = s` \\ gs[]
    \\ `DISJOINT s s1` by metis_tac[partitions_DISJOINT]
    \\ gs[IN_DISJOINT]
    \\ metis_tac[])
  \\ `subpart_history w b {e DIFF s; s} ⊆ subpart_history w b x`
  by (
    irule refines_subpart_history
    \\ metis_tac[subpart_domain_thm, is_subpartition_def] )
  \\ `{e DIFF s} partitions (e DIFF s)` by metis_tac[SING_partitions]
  \\ `e DIFF s ⊆ w` by gs[SUBSET_DEF]
  \\ `is_subpartition w {e DIFF s}` by (
    simp[is_subpartition_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ gs[])
  \\ `subpart_domain w {e DIFF s} = e DIFF s`
  by metis_tac[subpart_domain_thm]
  \\ `subpart_history w b {e DIFF s} = {}`
  by (
    DEP_REWRITE_TAC[subpart_history_eq_empty]
    \\ simp[is_subpartition_SING]
    \\ simp[indiscrete_partition_def])
  \\ `restrict_partition u (e DIFF s) = {e DIFF s}`
  by (
    gs[Abbr`u`, restrict_partition_def, IMAGE_EQ_SING]
    \\ rw[]
    \\ once_rewrite_tac[INTER_COMM]
    \\ once_rewrite_tac[GSYM SUBSET_INTER_ABSORPTION]
    \\ rw[SUBSET_DEF]
    \\ qmatch_goalsub_abbrev_tac`_ ∈ part vv _`
    \\ qmatch_goalsub_rename_tac`x1 ∈ part vv x2`
    \\ `x1 ∈ part vv x1` by metis_tac[in_part]
    \\ `part vv x1 = part vv x2` suffices_by metis_tac[]
    \\ irule part_unique
    \\ reverse conj_tac >- metis_tac[part_in_partition]
    \\ `part vv x1 ∈ vv` by metis_tac[part_in_partition]
    \\ gs[Abbr`vv`])
  \\ dsimp[]
  \\ Cases_on`v ∈ subpart_history w b x` \\ simp[]
  \\ conj_tac >- metis_tac[SUBSET_DEF]
  \\ `restrict_partition u s = restrict_partition y s`
  suffices_by metis_tac[]
  \\ `DISJOINT (e DIFF s) s` by metis_tac[IN_DIFF, IN_DISJOINT]
  \\ `∀x. x ∈ u ∧ x ∉ restrict_partition y s ⇒ DISJOINT x s`
  by dsimp[Abbr`u`]
  \\ pop_assum(mp_then Any mp_tac restrict_partition_remove_disjoint)
  \\ disch_then drule
  \\ impl_tac >- (
    simp[Abbr`u`]
    \\ gs[PSUBSET_DEF]
    \\ simp[SUBSET_DEF]
    \\ metis_tac[restrict_partition_partitions])
  \\ disch_then SUBST1_TAC
  \\ irule trivial_restrict_partition
  \\ irule restrict_partition_partitions
  \\ metis_tac[PSUBSET_DEF]
QED

Theorem subpart_history_common_refinement_BIGUNION_restrict:
  FINITE b ∧ b factorises w ∧ e ⊆ w ∧
  x ∈ sop ∧ (∀v. v ∈ sop ⇒ v partitions e)
  ⇒
  subpart_history w b (common_refinement e sop) =
  subpart_history w b x ∪
  BIGUNION
    (IMAGE (λz. subpart_history w b
                 (restrict_partition (common_refinement e (sop DELETE x)) z))
           x)
Proof
  strip_tac
  \\ drule subpart_history_binary_refinement_restrict
  \\ disch_then drule
  \\ `x partitions e` by metis_tac[]
  \\ disch_then drule
  \\ qmatch_goalsub_abbrev_tac`restrict_partition cfs _`
  \\ disch_then(qspec_then`cfs`mp_tac)
  \\ impl_tac
  >- simp[Abbr`cfs`, common_refinement_partitions]
  \\ disch_then (SUBST1_TAC o SYM)
  \\ `sop = x INSERT (sop DELETE x)` by metis_tac[INSERT_DELETE]
  \\ pop_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`x INSERT sx`
  \\ `x = common_refinement e {x}` by metis_tac[common_refinement_SING]
  \\ `{x; cfs} = IMAGE (common_refinement e) {{x}; sx}`
  by (
    simp[]
    \\ simp[Once EXTENSION]
    \\ metis_tac[])
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[common_refinement_IMAGE_common_refinement]
  \\ dsimp[]
  \\ conj_tac >- simp[Abbr`sx`]
  \\ metis_tac[INSERT_SING_UNION]
QED

Definition conditionally_orthogonal_def:
  conditionally_orthogonal w b x y z <=>
    FINITE b ∧ b factorises w ∧
    x partitions w ∧ y partitions w ∧ z partitions w ∧
    ∀s. s ∈ z ⇒
      DISJOINT (subpart_history w b (restrict_partition x s))
               (subpart_history w b (restrict_partition y s))
End

Theorem subpart_history_of_partition:
  FINITE b ∧ b factorises w ∧ v partitions w ⇒
  subpart_history w b v = history w b v
Proof
  rw[SET_EQ_SUBSET]
  >- (
    irule imp_subpart_history_SUBSET
    \\ rw[]
    >- (rw[is_subpartition_def] \\ metis_tac[SUBSET_REFL])
    \\ irule generates_partition_subpartition
    \\ metis_tac[history_thm])
  \\ `is_subpartition w v` by metis_tac[is_subpartition_def, SUBSET_REFL]
  \\ irule imp_history_SUBSET
  \\ rw[generates_partition_common_refinement_refines]
  >- rw[subpart_history_SUBSET_factorisation]
  \\ imp_res_tac subpart_history_thm
  \\ gs[generates_subpartition_common_refinement_refines]
  \\ qpat_x_assum`_ refines _`mp_tac
  \\ DEP_REWRITE_TAC[trivial_restrict_partition]
  \\ `subpart_domain w v = w` by metis_tac[subpart_domain_thm, SUBSET_REFL]
  \\ simp[common_refinement_partitions]
QED

Theorem conditionally_orthogonal_indiscrete:
  FINITE b ∧ b factorises w ∧
  x partitions w ∧ y partitions w ∧ orthogonal w b x y <=>
  conditionally_orthogonal w b x y (indiscrete_partition w)
Proof
  rw[conditionally_orthogonal_def, indiscrete_partition_partitions]
  \\ Cases_on`FINITE b` \\ rw[]
  \\ Cases_on`b factorises w` \\ rw[]
  \\ Cases_on`x partitions w` \\ rw[]
  \\ Cases_on`y partitions w` \\ rw[]
  \\ rw[indiscrete_partition_def]
  >- (
    gs[partitions_empty, orthogonal_def]
    \\ simp[history_eq_empty, indiscrete_partition_def] )
  \\ DEP_REWRITE_TAC[trivial_restrict_partition]
  \\ simp[subpart_history_of_partition, orthogonal_def]
QED

Theorem conditionally_orthogonal_sym:
  conditionally_orthogonal w b x y z <=>
  conditionally_orthogonal w b y x z
Proof
  rw[conditionally_orthogonal_def]
  \\ metis_tac[DISJOINT_SYM]
QED

Theorem conditionally_orthogonal_decomposition:
  (∀v. v ∈ sop ⇒ v partitions w) ∧
  conditionally_orthogonal w b x (common_refinement w sop) z ⇒
  ∀v. v ∈ sop ⇒ conditionally_orthogonal w b x v z
Proof
  rw[conditionally_orthogonal_def]
  \\ `subpart_history w b (restrict_partition v s) ⊆
      subpart_history w b (restrict_partition (common_refinement w sop) s)`
  suffices_by (
    gs[IN_DISJOINT, SUBSET_DEF]
    \\ metis_tac[])
  \\ DEP_REWRITE_TAC[restrict_partition_common_refinement]
  \\ simp[]
  \\ conj_asm1_tac >- metis_tac[partitions_thm]
  \\ DEP_REWRITE_TAC[subpart_history_common_refinement_BIGUNION]
  \\ simp[PULL_EXISTS, SUBSET_DEF]
  \\ metis_tac[subpart_domain_restrict, is_subpartition_restrict]
QED

Theorem conditionally_orthogonal_composition:
  FINITE b ∧ b factorises w ∧ x partitions w ∧ z partitions w ∧
  (∀v. v ∈ sop ⇒ conditionally_orthogonal w b x v z) ⇒
  conditionally_orthogonal w b x (common_refinement w sop) z
Proof
  rw[conditionally_orthogonal_def, common_refinement_partitions]
  \\ gs[]
  \\ DEP_REWRITE_TAC[restrict_partition_common_refinement]
  \\ simp[]
  \\ conj_asm1_tac >- metis_tac[partitions_thm]
  \\ DEP_REWRITE_TAC[subpart_history_common_refinement_BIGUNION]
  \\ simp[PULL_EXISTS]
  \\ metis_tac[is_subpartition_restrict, subpart_domain_restrict]
QED

Theorem subpart_history_empty[simp]:
  FINITE b ∧ b factorises w ⇒
  subpart_history w b {} = {}
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[subpart_history_eq_empty]
  \\ simp[]
  \\ conj_asm1_tac >- simp[is_subpartition_empty]
  \\ imp_res_tac subpart_domain_thm \\ fs[]
  \\ simp[indiscrete_partition_def]
QED

Theorem conditionally_orthogonal_contraction:
  conditionally_orthogonal w b x y z ∧
  conditionally_orthogonal w b x u (common_refinement w {y; z}) ⇒
  conditionally_orthogonal w b x (common_refinement w {y; u}) z
Proof
  strip_tac
  \\ simp[conditionally_orthogonal_def]
  \\ conj_asm1_tac >- fs[conditionally_orthogonal_def]
  \\ conj_asm1_tac >- fs[conditionally_orthogonal_def]
  \\ conj_asm1_tac >- fs[conditionally_orthogonal_def]
  \\ conj_asm1_tac >- fs[common_refinement_partitions]
  \\ conj_asm1_tac >- fs[conditionally_orthogonal_def]
  \\ qx_gen_tac`zz` \\ strip_tac
  \\ DEP_REWRITE_TAC[restrict_partition_common_refinement]
  \\ `u partitions w ∧ y partitions w` by fs[conditionally_orthogonal_def]
  \\ `zz ⊆ w` by metis_tac[partitions_thm]
  \\ conj_tac >- dsimp[]
  \\ simp[]
  \\ DEP_REWRITE_TAC[subpart_history_binary_refinement_restrict]
  \\ DEP_REWRITE_TAC[restrict_partition_partitions, FINITE_restrict_partition]
  \\ conj_tac >- ( dsimp[] \\ fs[conditionally_orthogonal_def, partitions_thm] )
  \\ conj_tac >- simp[]
  \\ simp[IN_DISJOINT, PULL_EXISTS]
  \\ conj_tac
  >- (
    fs[conditionally_orthogonal_def, IN_DISJOINT]
    \\ metis_tac[])
  \\ qx_gen_tac`yy`
  \\ strip_tac
  \\ DEP_REWRITE_TAC[restrict_restrict_partition]
  \\ conj_tac >- fs[restrict_partition_def]
  \\ fs[conditionally_orthogonal_def]
  \\ pop_assum mp_tac
  \\ simp[Once restrict_partition_def]
  \\ disch_then(qx_choose_then`a`strip_assume_tac)
  \\ `part y a ∈ y` by metis_tac[part_in_partition, SUBSET_DEF]
  \\ BasicProvers.VAR_EQ_TAC
  \\ qmatch_goalsub_abbrev_tac`yy ∩ zz`
  \\ `subpart_history w b (restrict_partition x zz) =
      subpart_history w b (restrict_partition x (yy ∩ zz))`
  by (
    `restrict_partition x (yy ∩ zz) =
     restrict_partition (restrict_partition x zz) (yy ∩ zz)`
    by ( DEP_REWRITE_TAC[restrict_restrict_partition] \\ simp[] )
    \\ pop_assum SUBST1_TAC
    \\ irule EQ_SYM
    \\ irule subpart_history_restrict
    \\ simp[]
    \\ qexists_tac`zz`
    \\ qexists_tac`restrict_partition y zz`
    \\ simp[]
    \\ DEP_REWRITE_TAC[restrict_partition_partitions]
    \\ simp[]
    \\ simp[restrict_partition_def]
    \\ qexists_tac`a` \\ simp[])
  \\ pop_assum SUBST1_TAC
  \\ fs[IN_DISJOINT]
  \\ simp[Once DISJ_COMM]
  \\ first_x_assum irule
  \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
  \\ dsimp[]
  \\ qexists_tac`a`
  \\ simp[]
  \\ `a ∈ w` by metis_tac[SUBSET_DEF]
  \\ `part z a = zz` by metis_tac[part_unique]
  \\ `yy ⊆ w` by metis_tac[partitions_thm]
  \\ simp[]
  \\ `yy ∩ zz ⊆ w` by fs[SUBSET_DEF]
  \\ metis_tac[SUBSET_INTER_ABSORPTION, INTER_COMM]
QED

Theorem conditionally_orthogonal_weak_union:
  (* consider sop = {y; u} for the binary version of weak union *)
  (!v. v ∈ sop ⇒ v partitions w) ∧
  conditionally_orthogonal w b x (common_refinement w sop) z ∧
  z ∉ sop ∧ y ∈ sop ∧ sop DELETE y <> {} ⇒
  conditionally_orthogonal w b x y
    (common_refinement w (z INSERT (sop DELETE y)))
Proof
  rw[conditionally_orthogonal_def]
  >- rw[common_refinement_partitions]
  \\ qmatch_asmsub_abbrev_tac`s ∈ common_refinement _ m`
  \\ qmatch_asmsub_abbrev_tac`m = z INSERT ww`
  \\ qabbrev_tac`www = common_refinement w ww`
  \\ `common_refinement w sop = common_refinement w {y; www}`
  by (
    `y = common_refinement w {y}` by metis_tac[common_refinement_SING]
    \\ pop_assum SUBST1_TAC
    \\ qunabbrev_tac`www`
    \\ `sop = BIGUNION {{y}; ww}`
    by ( rw[Abbr`ww`] \\ rw[Once EXTENSION] \\ metis_tac[] )
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[GSYM common_refinement_IMAGE_common_refinement]
    \\ dsimp[Abbr`ww`])
  \\ `www partitions w` by simp[Abbr`www`, common_refinement_partitions]
  \\ `∀s. s ∈ z ⇒ DISJOINT (subpart_history w b (restrict_partition x s))
                            (subpart_history w b (restrict_partition www s))`
  by (
    qx_gen_tac`zz`
    \\ strip_tac
    \\ `subpart_history w b (restrict_partition www zz) ⊆
        subpart_history w b (restrict_partition (common_refinement w {y; www}) zz)`
    suffices_by metis_tac[IN_DISJOINT, SUBSET_DEF]
    \\ `zz ⊆ w` by metis_tac[partitions_thm]
    \\ DEP_REWRITE_TAC[restrict_partition_common_refinement]
    \\ conj_tac >- dsimp[]
    \\ DEP_REWRITE_TAC[subpart_history_common_refinement_BIGUNION]
    \\ dsimp[is_subpartition_restrict, subpart_domain_restrict] )
  \\ qpat_x_assum`s ∈ _`mp_tac
  \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
  \\ conj_tac >- dsimp[Abbr`m`, Abbr`ww`]
  \\ simp[]
  \\ disch_then(qx_choose_then`a`strip_assume_tac)
  \\ BasicProvers.VAR_EQ_TAC
  \\ qmatch_goalsub_abbrev_tac`restrict_partition _ p`
  \\ `p = BIGINTER (IMAGE (λv. part v a) m)`
  by (
    simp[Abbr`p`]
    \\ simp[Once INTER_COMM]
    \\ irule (SUBSET_INTER_ABSORPTION |> SPEC_ALL |> EQ_IMP_RULE |> #1)
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ dsimp[Abbr`m`]
    \\ metis_tac[part_in_partition, partitions_thm, SUBSET_DEF] )
  \\ simp[Abbr`p`] \\ pop_assum kall_tac
  \\ simp[Abbr`m`]
  \\ qmatch_goalsub_abbrev_tac`part z a ∩ pw`
  \\ `pw = part www a`
  by (
    irule part_unique
    \\ reverse conj_tac
    >- (
      reverse conj_tac >- metis_tac[]
      \\ simp[Abbr`www`]
      \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
      \\ dsimp[Abbr`ww`, Abbr`pw`]
      \\ qexists_tac`a` \\ simp[]
      \\ simp[Once INTER_COMM]
      \\ irule (SUBSET_INTER_ABSORPTION |> SPEC_ALL |> EQ_IMP_RULE |> #1 |> GSYM)
      \\ simp[SUBSET_DEF, PULL_EXISTS]
      \\ fs[GSYM MEMBER_NOT_EMPTY] \\ rw[] \\ res_tac
      \\ metis_tac[part_in_partition, partitions_thm, SUBSET_DEF] )
    \\ simp[Abbr`pw`, PULL_EXISTS]
    \\ rw[]
    \\ irule in_part
    \\ fs[Abbr`ww`]
    \\ metis_tac[])
  \\ fs[Abbr`pw`] \\ pop_assum kall_tac
  \\ `part z a ∈ z` by metis_tac[part_in_partition]
  \\ `part z a ⊆ w` by metis_tac[partitions_thm]
  \\ `subpart_history w b (restrict_partition x (part z a ∩ part www a)) =
      subpart_history w b (restrict_partition x (part z a))`
  by (
    qpat_assum`x partitions w`(mp_then Any mp_tac restrict_restrict_partition)
    \\ disch_then(qspecl_then[`part z a INTER part www a`,`part z a`]mp_tac)
    \\ impl_keep_tac >- metis_tac[partitions_thm, INTER_SUBSET]
    \\ disch_then(SUBST1_TAC o SYM)
    \\ irule subpart_history_restrict
    \\ rpt (conj_tac >- simp[])
    \\ qexistsl_tac[`part z a`, `restrict_partition www (part z a)`]
    \\ conj_tac >- simp[]
    \\ DEP_REWRITE_TAC[restrict_partition_partitions]
    \\ simp[]
    \\ simp[restrict_partition_def]
    \\ qexists_tac`a` \\ simp[INTER_COMM]
    \\ metis_tac[in_part])
  \\ pop_assum SUBST1_TAC
  \\ last_x_assum(qspec_then`part z a`mp_tac)
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`DISJOINT s1 s2 ⇒ DISJOINT _ s3`
  \\ `s3 ⊆ s2` suffices_by metis_tac[IN_DISJOINT, SUBSET_DEF]
  \\ simp[Abbr`s3`, Abbr`s2`]
  \\ qmatch_goalsub_abbrev_tac`zz ∩ uu`
  \\ `uu ∈ www` by metis_tac[part_in_partition]
  \\ DEP_REWRITE_TAC[restrict_partition_common_refinement] \\ conj_tac >- dsimp[]
  \\ `{y; www} = {www; y}` by (simp[Once EXTENSION] \\ metis_tac[])
  \\ pop_assum SUBST1_TAC
  \\ simp[]
  \\ DEP_REWRITE_TAC[subpart_history_binary_refinement_restrict]
  \\ DEP_REWRITE_TAC[restrict_partition_partitions, FINITE_restrict_partition]
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ gen_tac
  \\ Cases_on`zz ∩ uu = {}` \\ simp[]
  \\ strip_tac
  \\ disj2_tac
  \\ qexists_tac`zz ∩ uu`
  \\ DEP_REWRITE_TAC[restrict_restrict_partition]
  \\ simp[]
  \\ simp[restrict_partition_def]
  \\ fs[GSYM MEMBER_NOT_EMPTY]
  \\ qmatch_asmsub_rename_tac`q ∈ uu`
  \\ qexists_tac`q` \\ simp[]
  \\ simp[Once INTER_COMM]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule part_unique
  \\ metis_tac[SUBSET_DEF]
QED

Theorem conditionally_orthogonal_self_refines:
  conditionally_orthogonal w b x x y <=>
  FINITE b ∧ b factorises w ∧ x partitions w ∧ y partitions w ∧ y refines x
Proof
  rw[conditionally_orthogonal_def]
  \\ Cases_on`FINITE b ∧ b factorises w ∧ x partitions w ∧ y partitions w` \\ gs[]
  \\ rw[EQ_IMP_THM]
  >- (
    DEP_REWRITE_TAC[refines_grows_parts] \\ simp[]
    \\ qx_genl_tac[`s`,`t`] \\ strip_tac
    \\ `part y s ∈ y ∧ part y t ∈ y` by metis_tac[part_in_partition]
    \\ `part y s ⊆ w ∧ part y t ⊆ w` by metis_tac[partitions_thm]
    \\ `restrict_partition x (part y s) = indiscrete_partition (part y s)`
    by metis_tac[subpart_history_eq_empty,
                 subpart_domain_restrict, is_subpartition_restrict]
    \\ `s ∈ part y s ∧ t ∈ part y t` by metis_tac[in_part]
    \\ gs[]
    \\ fs[indiscrete_partition_def]
    \\ Cases_on`part y t = {}` \\ gs[]
    \\ fs[restrict_partition_def, IMAGE_EQ_SING]
    \\ fs[Once INTER_COMM]
    \\ fs[GSYM SUBSET_INTER_ABSORPTION]
    \\ irule part_unique
    \\ reverse conj_tac >- metis_tac[part_in_partition]
    \\ metis_tac[SUBSET_DEF])
  \\ DEP_REWRITE_TAC[subpart_history_eq_empty]
  \\ DEP_REWRITE_TAC[is_subpartition_restrict, subpart_domain_restrict]
  \\ simp[]
  \\ conj_asm1_tac >- metis_tac[partitions_thm]
  \\ rw[indiscrete_partition_def]
  \\ qpat_x_assum`_ refines _`mp_tac
  \\ DEP_REWRITE_TAC[refines_grows_parts] \\ simp[]
  \\ simp[restrict_partition_def, IMAGE_EQ_SING]
  \\ simp[Once INTER_COMM]
  \\ simp[GSYM SUBSET_INTER_ABSORPTION]
  \\ simp[SUBSET_DEF]
  \\ strip_tac
  \\ qx_gen_tac`a` \\ strip_tac
  \\ qx_gen_tac`z` \\ strip_tac
  \\ `s = part y a` by metis_tac[part_unique, SUBSET_DEF]
  \\ `s = part y z` by metis_tac[part_unique, SUBSET_DEF]
  \\ first_x_assum(qspecl_then[`a`,`z`]mp_tac)
  \\ impl_tac >- fs[SUBSET_DEF]
  \\ metis_tac[in_part, SUBSET_DEF]
QED

val _ = export_theory();
