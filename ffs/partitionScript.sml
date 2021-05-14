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

open HolKernel boolLib bossLib Parse dep_rewrite
     arithmeticTheory pred_setTheory pairTheory listTheory
     helperSetTheory

val _ = new_theory"partition";

Definition BIGdisjUNION_def:
  BIGdisjUNION sos = { (s, x) | s IN sos /\ x IN s }
End

Theorem BINARY_BIGdisjUNION:
  a <> b ==>
  BIJ (\(s, x). (if s = a then INL else INR) x)
    (BIGdisjUNION {a; b}) (disjUNION a b)
Proof
  rw[BIJ_IFF_INV]
  >- ( fs[BIGdisjUNION_def] \\ rw[] )
  \\ qexists_tac`\x. sum_CASE x (\y. (a,y)) (\y. (b,y))`
  \\ rw[BIGdisjUNION_def, disjUNION_def]
  \\ rw[]
QED

Theorem partitions_BIJ_BIGdisjUNION:
  v partitions w <=>
    BIJ SND (BIGdisjUNION v) w /\ {} NOTIN v
Proof
  reverse(Cases_on`BIGUNION v ⊆ w`)
  >- (
    `¬(v partitions w)` by ( fs[partitions_thm, SUBSET_DEF] \\ METIS_TAC[] )
    \\ simp[]
    \\ Cases_on`{} IN v` \\ simp[]
    \\ strip_tac
    \\ fs[BIJ_DEF, INJ_DEF]
    \\ fs[SUBSET_DEF, BIGdisjUNION_def, PULL_EXISTS]
    \\ metis_tac[])
  \\ `!x. x IN (BIGdisjUNION v) ==> SND x IN w`
  by (
    rw[BIGdisjUNION_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[])
  \\ reverse eq_tac
  >- (
    rw[partitions_thm]
    >- metis_tac[]
    >- (fs[SUBSET_DEF, PULL_EXISTS] \\ METIS_TAC[])
    \\ simp[EXISTS_UNIQUE_ALT]
    \\ fs[BIJ_IFF_INV]
    \\ qexists_tac`FST (g y)`
    \\ fs[BIGdisjUNION_def, PULL_EXISTS]
    \\ res_tac \\ fs[]
    \\ strip_tac \\ reverse eq_tac >- metis_tac[]
    \\ strip_tac \\ res_tac \\ fs[])
  \\ strip_tac
  \\ imp_res_tac partitions_thm
  \\ reverse conj_tac >- metis_tac[]
  \\ simp[BIJ_IFF_INV]
  \\ qexists_tac`\x. (part v x, x)`
  \\ fs[BIGdisjUNION_def]
  \\ conj_tac >- metis_tac[in_part, part_in_partition]
  \\ rw[PULL_EXISTS]
  \\ metis_tac[part_unique, SUBSET_DEF]
QED

Definition discrete_partition_def:
  discrete_partition s = {{x} | x IN s}
End

Theorem equiv_class_equal:
  !z s. z IN s ==> equiv_class (=) s z = {z}
Proof
  rw[EXTENSION]
  \\ metis_tac[]
QED

Theorem discrete_partition_partitions:
  discrete_partition s partitions s
Proof
  rw[partitions_def]
  \\ qexists_tac`(=)`
  \\ rw[partition_def, equiv_on_def]
  >- metis_tac[]
  \\ rw[discrete_partition_def, Once EXTENSION]
  \\ AP_TERM_TAC
  \\ simp[Once FUN_EQ_THM]
  \\ metis_tac[equiv_class_equal]
QED

Theorem part_discrete_partition:
  x IN s ==>
  part (discrete_partition s) x = {x}
Proof
  rw[part_def, discrete_partition_def]
  \\ SELECT_ELIM_TAC \\ rw[PULL_EXISTS]
  \\ fs[]
QED

Definition indiscrete_partition_def:
  indiscrete_partition s = if s = {} then {} else {s}
End

Theorem indiscrete_partition_partitions:
  indiscrete_partition s partitions s
Proof
  rw[partitions_thm, indiscrete_partition_def]
  \\ rw[EXISTS_UNIQUE_THM]
QED

Theorem discrete_refines:
  v partitions w ==> discrete_partition w refines v
Proof
  rw[refines_def, discrete_partition_def, SUBSET_DEF] \\ rw[]
  \\ metis_tac[part_in_partition, in_part]
QED

Theorem refines_indiscrete:
  v partitions w ==> v refines indiscrete_partition w
Proof
  rw[refines_def, indiscrete_partition_def, partitions_empty]
  \\ metis_tac[partitions_thm]
QED

Definition common_refinement_def:
  common_refinement w sop =
    partition (\x y. (!v. v IN sop ==> part v x = part v y)) w
End

Theorem common_refinement_partitions:
  common_refinement w sop partitions w
Proof
  rw[common_refinement_def]
  \\ rw[partitions_def]
  \\ qmatch_goalsub_abbrev_tac`partition R`
  \\ qexists_tac`R` \\ rw[]
  \\ rw[equiv_on_def, Abbr`R`]
  \\ metis_tac[]
QED

Theorem common_refinement_refines:
  (!v. v IN sop ==> v partitions w) /\ v IN sop
  ==> common_refinement w sop refines v
Proof
  strip_tac
  \\ assume_tac common_refinement_partitions
  \\ `v partitions w` by metis_tac[]
  \\ DEP_REWRITE_TAC[refines_grows_parts]
  \\ simp[]
  \\ rpt gen_tac \\ strip_tac
  \\ fs[common_refinement_def]
  \\ qmatch_asmsub_abbrev_tac`partition R`
  \\ `R equiv_on w`
  by ( simp[equiv_on_def, Abbr`R`] \\ metis_tac[] )
  \\ `{ a | a IN w /\ R a x } = { a | a IN w /\ R a y }`
  by metis_tac[part_partition]
  \\ pop_assum mp_tac
  \\ simp[Once EXTENSION]
  \\ strip_tac
  \\ `R x y` by metis_tac[equiv_on_def]
  \\ fs[Abbr`R`]
QED

Theorem common_refinement_empty:
  common_refinement w {} = indiscrete_partition w
Proof
  rw[common_refinement_def, partition_def, indiscrete_partition_def]
  \\ rw[Once EXTENSION]
  \\ fs[GSYM MEMBER_NOT_EMPTY]
  \\ metis_tac[]
QED

Theorem same_part_common_refinement:
  x IN w /\ y IN w /\ (!v. v IN sop ==> part v x = part v y) ==>
  part (common_refinement w sop) x =
  part (common_refinement w sop) y
Proof
  rw[common_refinement_def]
  \\ DEP_REWRITE_TAC[part_partition]
  \\ rw[]
  \\ rw[equiv_on_def]
  \\ metis_tac[]
QED

Theorem same_part_common_refinement_iff:
  x IN w /\ y IN w /\ (!v. v IN sop ==> v partitions w) ==>
  ((part (common_refinement w sop) x =
   part (common_refinement w sop) y) <=>
   (!v. v IN sop ==> part v x = part v y))
Proof
  strip_tac
  \\ reverse eq_tac
  >- metis_tac[same_part_common_refinement]
  \\ strip_tac
  \\ assume_tac common_refinement_partitions
  \\ rpt strip_tac
  \\ irule part_unique
  \\ reverse conj_tac >- metis_tac[part_in_partition]
  \\ drule common_refinement_refines
  \\ disch_then drule
  \\ metis_tac[in_part, refines_grows_parts]
QED

Theorem refines_common_refinement:
  v partitions w /\ (!x. x IN sop ==> x partitions w /\ v refines x)
  ==>
  v refines common_refinement w sop
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[refines_grows_parts]
  \\ simp[common_refinement_partitions]
  \\ rpt strip_tac
  \\ irule same_part_common_refinement
  \\ simp[]
  \\ qx_gen_tac`z` \\ strip_tac
  \\ metis_tac[refines_grows_parts]
QED

Theorem common_refinement_SUBSET:
  c SUBSET d ∧ (!v. v ∈ d ⇒ v partitions w) ==>
  common_refinement w d refines common_refinement w c
Proof
  strip_tac
  \\ irule refines_common_refinement
  \\ simp[common_refinement_partitions]
  \\ fs[SUBSET_DEF]
  \\ metis_tac[common_refinement_refines]
QED

Theorem common_refinement_SING:
  v partitions w ⇒
  common_refinement w {v} = v
Proof
  strip_tac
  \\ irule refines_antisym
  \\ conj_tac >- metis_tac[common_refinement_partitions]
  \\ simp[common_refinement_refines]
  \\ irule refines_common_refinement
  \\ simp[]
QED

(* not very useful? *)
Theorem IN_common_refinement:
  (∀v. v ∈ b ⇒ v partitions w) ∧ s ∈ common_refinement w b ⇒
  ∀v. v ∈ b ⇒ ∃!t. t ∈ v ∧ s ⊆ t
Proof
  rw[]
  \\ `common_refinement w b partitions w`
  by metis_tac[common_refinement_partitions]
  \\ `s ≠ {} ∧ s ⊆ w` by metis_tac[partitions_thm]
  \\ `∃x. x ∈ s ∧ x ∈ w` by metis_tac[MEMBER_NOT_EMPTY, SUBSET_DEF]
  \\ `s = part (common_refinement w b) x` by metis_tac[part_unique]
  \\ `common_refinement w b refines v`
  by metis_tac[common_refinement_refines]
  \\ `∃s2. s2 ∈ v ∧ s ⊆ s2` by metis_tac[refines_def]
  \\ `s2 = part v x` by metis_tac[part_unique, SUBSET_DEF]
  \\ simp[EXISTS_UNIQUE_THM]
  \\ conj_tac >- metis_tac[]
  \\ rpt strip_tac
  \\ metis_tac[part_unique, SUBSET_DEF]
QED

Theorem common_refinement_eq_empty:
  common_refinement w b = {} <=> w = {}
Proof
  rw[common_refinement_def, partition_def, EQ_IMP_THM]
  \\ fs[Once EXTENSION]
QED

(* subpartitions *)

Definition is_subpartition_def:
  is_subpartition w x <=> ?e. e ⊆ w ∧ x partitions e
End

Definition subpart_domain_def:
  subpart_domain w x = @e. e ⊆ w ∧ x partitions e
End

Theorem subpart_domain_thm:
  is_subpartition w x ⇒
  (∀e. e ⊆ w ∧ x partitions e ⇔ e = subpart_domain w x)
Proof
  rw[subpart_domain_def]
  \\ SELECT_ELIM_TAC \\ rw[]
  \\ fs[is_subpartition_def]
  >- metis_tac[]
  \\ rw[EQ_IMP_THM]
  \\ fs[partitions_def]
  \\ imp_res_tac BIGUNION_partition
  \\ gs[]
QED

Definition restrict_partition_def:
  restrict_partition v e = IMAGE (λx. part v x ∩ e) e
End

Theorem restrict_partition_partitions:
  v partitions w ∧ e ⊆ w ⇒
  restrict_partition v e partitions e
Proof
  rw[restrict_partition_def]
  \\ fs[partitions_def]
  \\ imp_res_tac equiv_on_subset
  \\ qexists_tac`R`
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  >- (
    fs[SUBSET_DEF]
    \\ rw[part_partition]
    \\ rw[partition_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[Once EXTENSION]
    \\ metis_tac[equiv_on_def])
  \\ fs[partition_element]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ fs[SUBSET_DEF]
  \\ simp[part_partition]
  \\ simp[Once EXTENSION]
  \\ metis_tac[equiv_on_def]
QED

Theorem part_restrict_partition:
  v partitions w ∧ e ⊆ w ∧ x ∈ e ⇒
  part (restrict_partition v e) x = part v x ∩ e
Proof
  strip_tac
  \\ imp_res_tac restrict_partition_partitions
  \\ irule EQ_SYM
  \\ irule part_unique
  \\ simp[]
  \\ `x ∈ w` by fs[SUBSET_DEF]
  \\ conj_tac >- metis_tac[in_part]
  \\ reverse conj_tac >- metis_tac[]
  \\ simp[restrict_partition_def]
  \\ metis_tac[]
QED

Theorem partition_is_subpartition:
  v partitions w ⇒
  is_subpartition w v ∧
  subpart_domain w v = w
Proof
  strip_tac
  \\ conj_asm1_tac >-
    (rw[is_subpartition_def] \\ metis_tac[SUBSET_REFL])
  \\ metis_tac[subpart_domain_thm, SUBSET_REFL]
QED

Theorem is_subpartition_common_refinement:
  e ⊆ w
  ⇒
  is_subpartition w (common_refinement e sop) ∧
  subpart_domain w (common_refinement e sop) = e
Proof
  strip_tac
  \\ conj_asm1_tac
  >- (
    simp[is_subpartition_def]
    \\ qexists_tac`e` \\ simp[common_refinement_partitions])
  \\ simp[GSYM subpart_domain_thm, common_refinement_partitions]
QED

Theorem restrict_discrete_partition:
  e ⊆ w ⇒
  restrict_partition (discrete_partition w) e = discrete_partition e
Proof
  rw[restrict_partition_def]
  \\ fs[SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  >- ( gs[part_discrete_partition]
       \\ rw[SING_INTER]
       \\ gs[discrete_partition_def])
  \\ qexists_tac`CHOICE x`
  \\ pop_assum mp_tac
  \\ simp[Once discrete_partition_def]
  \\ strip_tac \\ rw[]
  \\ simp[part_discrete_partition]
  \\ rw[SING_INTER]
QED

Theorem part_indiscrete_partition:
  x ∈ w ⇒
  part (indiscrete_partition w) x = w
Proof
  rw[indiscrete_partition_def]
  \\ rw[part_def]
  \\ SELECT_ELIM_TAC
  \\ rw[]
QED

Theorem restrict_indiscrete_partition:
  e ⊆ w  ⇒
  restrict_partition (indiscrete_partition w) e = indiscrete_partition e
Proof
  rw[indiscrete_partition_def]
  \\ rw[restrict_partition_def]
  \\ rw[IMAGE_EQ_SING]
  \\ `x ∈ w` by metis_tac[SUBSET_DEF]
  \\ drule part_indiscrete_partition
  \\ rw[indiscrete_partition_def]
  \\ irule SUBSET_INTER2
  \\ rw[]
QED

Theorem is_subpartition_indiscrete:
  e ⊆ w ⇒
  is_subpartition w (indiscrete_partition e)
Proof
  rw[is_subpartition_def]
  \\ qexists_tac`e`
  \\ rw[indiscrete_partition_partitions]
QED

Theorem subpart_domain_indiscrete:
  e ⊆ w ⇒
  subpart_domain w (indiscrete_partition e) = e
Proof
  strip_tac
  \\ imp_res_tac is_subpartition_indiscrete
  \\ drule subpart_domain_thm
  \\ metis_tac[indiscrete_partition_partitions]
QED

Theorem imp_restrict_partition_refines:
  v1 refines v2 ∧ v1 partitions w ∧ v2 partitions w ∧ e ⊆ w ⇒
  restrict_partition v1 e refines restrict_partition v2 e
Proof
  rw[refines_def]
  \\ gs[restrict_partition_def, PULL_EXISTS]
  \\ qexists_tac`x` \\ simp[]
  \\ `x ∈ w` by metis_tac[SUBSET_DEF]
  \\ `part v1 x ∈ v1` by metis_tac[part_in_partition]
  \\ `∃s2. s2 ∈ v2 ∧ part v1 x ⊆ s2` by metis_tac[]
  \\ `x ∈ part v1 x` by metis_tac[in_part]
  \\ `x ∈ s2` by metis_tac[SUBSET_DEF]
  \\ `s2 = part v2 x` by metis_tac[part_unique]
  \\ gs[SUBSET_DEF]
QED

Theorem trivial_restrict_partition:
  v partitions w ⇒
  restrict_partition v w = v
Proof
  rw[restrict_partition_def, Once SET_EQ_SUBSET, SUBSET_DEF]
  >- (
    qmatch_asmsub_rename_tac`x ∈ w`
    \\ `part v x ∈ v` by metis_tac[part_in_partition]
    \\ `part v x ⊆ w` by metis_tac[partitions_thm]
    \\ `part v x ∩ w = part v x` by metis_tac[SUBSET_INTER_ABSORPTION]
    \\ metis_tac[])
  \\ `x <> {}` by metis_tac[partitions_thm]
  \\ `∃z. z ∈ x` by metis_tac[MEMBER_NOT_EMPTY]
  \\ qexists_tac`z`
  \\ `x ⊆ w` by metis_tac[partitions_thm]
  \\ reverse conj_asm2_tac >- metis_tac[SUBSET_DEF]
  \\ `x = part v z` by metis_tac[part_unique]
  \\ simp[]
  \\ simp[GSYM SUBSET_INTER_ABSORPTION]
  \\ metis_tac[partitions_thm]
QED

Theorem restrict_refinement_refines:
  (!v. v IN sop ==> v partitions w) ∧ e ⊆ w ⇒
  restrict_partition (common_refinement w sop) e refines
  common_refinement e (IMAGE (\v. restrict_partition v e) sop)
Proof
  strip_tac
  \\ irule refines_common_refinement
  \\ simp[PULL_EXISTS]
  \\ reverse conj_tac
  >- (
    irule restrict_partition_partitions
    \\ qexists_tac`w`
    \\ simp[common_refinement_partitions] )
  \\ gen_tac \\ strip_tac
  \\ conj_tac >- metis_tac[restrict_partition_partitions]
  \\ irule imp_restrict_partition_refines
  \\ metis_tac[common_refinement_refines, common_refinement_partitions]
QED

Theorem is_subpartition_discrete:
  e ⊆ w ⇒
  is_subpartition w (discrete_partition e)
Proof
  rw[is_subpartition_def]
  \\ metis_tac[discrete_partition_partitions]
QED

Theorem subpart_domain_discrete:
  e ⊆ w ⇒
  subpart_domain w (discrete_partition e) = e
Proof
  strip_tac
  \\ metis_tac[subpart_domain_thm,
               discrete_partition_partitions,
               is_subpartition_discrete]
QED

Theorem is_subpartition_empty:
  is_subpartition w {}
Proof
  rw[is_subpartition_def]
QED

Theorem discrete_partition_empty[simp]:
  discrete_partition {} = {}
Proof
  rw[discrete_partition_def]
QED

Theorem is_subpartition_SING:
  is_subpartition w {v} ⇔ v ⊆ w ∧ v ≠ ∅
Proof
  rw[is_subpartition_def, SING_partitions]
QED

Theorem refines_discrete:
  v partitions w ⇒
  (v refines discrete_partition w ⇔ v = discrete_partition w)
Proof
  strip_tac
  \\ rw[EQ_IMP_THM]
  \\ irule refines_antisym
  \\ rw[discrete_refines]
  \\ metis_tac[discrete_partition_partitions]
QED

Theorem discrete_partition_as_partition:
  discrete_partition w = partition (=) w
Proof
  rw[discrete_partition_def, partition_def]
  \\ rw[SET_EQ_SUBSET, PULL_EXISTS, SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem discrete_eq_indiscrete_SUBSET_SING:
  (discrete_partition w = indiscrete_partition w) <=> ∃x. w ⊆ {x}
Proof
  rw[discrete_partition_def, indiscrete_partition_def]
  \\ rw[EQ_IMP_THM]
  \\ fs[Once SET_EQ_SUBSET]
  \\ rw[Once SET_EQ_SUBSET]
  \\ gs[SUBSET_DEF, PULL_EXISTS]
  \\ rw[]
  \\ rw[Once SET_EQ_SUBSET]
  \\ rw[SUBSET_DEF]
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Theorem is_subpartition_restrict:
  v partitions w ∧ e ⊆ w ⇒
  is_subpartition w (restrict_partition v e)
Proof
  rw[is_subpartition_def]
  \\ metis_tac[restrict_partition_partitions]
QED

Theorem subpart_domain_restrict:
  v partitions w ∧ e ⊆ w ⇒
  subpart_domain w (restrict_partition v e) = e
Proof
  strip_tac
  \\ imp_res_tac is_subpartition_restrict
  \\ metis_tac[restrict_partition_partitions, subpart_domain_thm]
QED

Theorem common_refinement_BIGINTER:
  (∀v. v ∈ sop ⇒ v partitions w) ⇒
  common_refinement w sop =
  IMAGE (λx. w ∩ BIGINTER (IMAGE (λv. part v x) sop)) w
Proof
  rw[common_refinement_def]
  \\ rw[Once EXTENSION]
  \\ rw[EQ_IMP_THM, partition_def]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[Once EXTENSION, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  \\ metis_tac[in_part, part_in_partition, part_unique]
QED

Theorem FINITE_restrict_partition:
  v partitions w ∧ e ⊆ w ∧ FINITE v ⇒ FINITE (restrict_partition v e)
Proof
  rw[restrict_partition_def]
  \\ irule SUBSET_FINITE
  \\ qexists_tac`IMAGE (λp. p ∩ e) v`
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ qx_gen_tac`z` \\ rw[]
  \\ qexists_tac`part v z`
  \\ simp[]
  \\ irule part_in_partition
  \\ metis_tac[SUBSET_DEF]
QED

Theorem restrict_partition_common_refinement:
  (!v. v IN sop ==> v partitions w) ∧ e ⊆ w ⇒
  restrict_partition (common_refinement w sop) e =
  common_refinement e (IMAGE (\v. restrict_partition v e) sop)
Proof
  strip_tac
  \\ Cases_on`sop = {}` \\ gs[]
  >- (
    simp[common_refinement_empty]
    \\ irule restrict_indiscrete_partition
    \\ simp[] )
  \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
  \\ simp[PULL_EXISTS]
  \\ conj_tac >- metis_tac[restrict_partition_partitions]
  \\ rw[restrict_partition_def]
  \\ irule IMAGE_CONG
  \\ simp[]
  \\ qx_gen_tac`x` \\ strip_tac
  \\ simp[GSYM IMAGE_COMPOSE, combinTheory.o_DEF]
  \\ gs[GSYM restrict_partition_def]
  \\ simp[Once INTER_COMM]
  \\ qmatch_goalsub_abbrev_tac`part iv x`
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ qx_gen_tac`y`
  \\ Cases_on`y ∈ e` \\ simp[]
  \\ gs[GSYM common_refinement_BIGINTER]
  \\ `iv partitions w` by metis_tac[common_refinement_partitions]
  \\ `∀v. v ∈ sop ⇒ iv refines v` by metis_tac[common_refinement_refines]
  \\ `x ∈ w ∧ y ∈ w` by metis_tac[SUBSET_DEF]
  \\ `∀v. v ∈ sop ∧ part iv x = part iv y ⇒ part v x = part v y`
  by metis_tac[refines_grows_parts]
  \\ `y ∈ part iv x <=> (part iv x = part iv y)`
  by (
    reverse(rw[EQ_IMP_THM])
    >- metis_tac[in_part]
    \\ irule part_unique
    \\ metis_tac[part_in_partition])
  \\ pop_assum SUBST1_TAC
  \\ eq_tac >> rw[]
  >- (
    DEP_REWRITE_TAC[part_restrict_partition]
    \\ rw[] \\ metis_tac[in_part] )
  \\ qunabbrev_tac`iv`
  \\ DEP_REWRITE_TAC[same_part_common_refinement_iff]
  \\ rw[]
  \\ first_x_assum drule
  \\ DEP_REWRITE_TAC[part_restrict_partition]
  \\ rw[]
  \\ irule part_unique
  \\ metis_tac[part_in_partition]
QED

Theorem restrict_restrict_partition:
  v partitions w ∧ s2 ⊆ s1 ∧ s1 ⊆ w ⇒
  restrict_partition (restrict_partition v s1) s2 =
  restrict_partition v s2
Proof
  rw[restrict_partition_def]
  \\ rw[Once EXTENSION]
  \\ rw[GSYM restrict_partition_def]
  \\ `restrict_partition v s1 partitions s1` by metis_tac[restrict_partition_partitions]
  \\ AP_TERM_TAC
  \\ simp[Once FUN_EQ_THM]
  \\ qx_gen_tac`s`
  \\ Cases_on`s ∈ s2` \\ simp[]
  \\ DEP_REWRITE_TAC[part_restrict_partition]
  \\ conj_tac >- metis_tac[SUBSET_DEF]
  \\ qmatch_goalsub_abbrev_tac`x = a <=> x = b`
  \\ `a = b` suffices_by rw[]
  \\ simp[Abbr`a`, Abbr`b`]
  \\ simp[Once EXTENSION]
  \\ metis_tac[SUBSET_DEF]
QED

Theorem pull_out_partition:
  v partitions w ∧ x PSUBSET w ⇒
  w DIFF x INSERT restrict_partition v x partitions w
Proof
  strip_tac
  \\ dsimp[restrict_partition_def, partitions_thm]
  \\ simp[GSYM CONJ_ASSOC]
  \\ simp[SUBSET_DIFF_EMPTY]
  \\ conj_asm1_tac >- metis_tac[SUBSET_ANTISYM, PSUBSET_DEF]
  \\ conj_asm1_tac
  >- (
    simp[GSYM MEMBER_NOT_EMPTY]
    \\ qx_gen_tac`z` \\ strip_tac
    \\ qexists_tac`z`
    \\ metis_tac[in_part, PSUBSET_DEF, SUBSET_DEF])
  \\ conj_asm1_tac
  >- metis_tac[PSUBSET_DEF, SUBSET_INTER_SUBSET, INTER_COMM]
  \\ rw[]
  \\ simp[EXISTS_UNIQUE_THM]
  \\ conj_tac
  >- (
    qexists_tac`if y IN x then part v y INTER x else w DIFF x`
    \\ IF_CASES_TAC \\ simp[]
    \\ `y ∈ part v y` by metis_tac[in_part]
    \\ metis_tac[])
  \\ rw[] \\ fs[]
  \\ `∀z. z ∈ x ⇒ z ∈ w` by metis_tac[PSUBSET_DEF, SUBSET_DEF]
  \\ metis_tac[part_unique, part_in_partition]
QED

Theorem binary_partition:
  x <> {} /\ x PSUBSET w ⇒
  {x; w DIFF x} partitions w
Proof
  rw[partitions_thm, PSUBSET_DEF] \\ rw[]
  >- (
    gs[GSYM MEMBER_NOT_EMPTY]
    \\ metis_tac[SUBSET_DEF, SET_EQ_SUBSET])
  \\ dsimp[EXISTS_UNIQUE_THM]
  \\ metis_tac[]
QED

Theorem restrict_partition_remove_disjoint:
  v partitions w ∧ e ⊆ w ∧ u partitions e ∧
  u ⊆ v ∧ (∀x. x ∈ v ∧ x ∉ u ⇒ DISJOINT x e) ⇒
  restrict_partition v e = restrict_partition u e
Proof
  rw[restrict_partition_def]
  \\ simp[Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qmatch_asmsub_rename_tac`x ∈ e`
  \\ `x ∈ w` by metis_tac[SUBSET_DEF]
  \\ `part v x ∈ v ∧ x ∈ part v x` by metis_tac[in_part, part_in_partition]
  \\ `part u x ∈ u ∧ x ∈ part u x` by metis_tac[in_part, part_in_partition]
  \\ (Cases_on`part v x ∈ u`
      >- ( `part v x = part u x` by metis_tac[part_unique] \\ gs[] ))
  \\ metis_tac[IN_DISJOINT]
QED

Theorem common_refinement_IMAGE_common_refinement:
  (∀sop. sop ∈ sosp ⇒ ∀v. v ∈ sop ⇒ v partitions w) ⇒
  common_refinement w (IMAGE (common_refinement w) sosp) =
  common_refinement w (BIGUNION sosp)
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[common_refinement_BIGINTER]
  \\ simp[PULL_EXISTS, common_refinement_partitions]
  \\ conj_tac >- metis_tac[]
  \\ rw[Once EXTENSION, EQ_IMP_THM]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[Once EXTENSION, EQ_IMP_THM] \\ gs[PULL_EXISTS]
  \\ TRY (
    qmatch_goalsub_rename_tac`x ∈ part (common_refinement w sop) z`
    \\ `part (common_refinement w sop) z = part (common_refinement w sop) x`
    by (
      irule same_part_common_refinement
      \\ rw[]
      \\ irule part_unique
      \\ rw[]
      \\ metis_tac[part_in_partition] )
    \\ rw[]
    \\ irule in_part
    \\ metis_tac[common_refinement_partitions])
  \\ qmatch_goalsub_rename_tac`x ∈ part v y`
  \\ `part v y = part v x` suffices_by metis_tac[in_part]
  \\ `part (common_refinement w s) y = part (common_refinement w s) x`
  suffices_by metis_tac[same_part_common_refinement_iff]
  \\ irule part_unique
  \\ metis_tac[part_in_partition, common_refinement_partitions]
QED

Theorem restrict_partition_to_empty[simp]:
  restrict_partition v {} = {}
Proof
  rw[restrict_partition_def]
QED

val _ = export_theory();
