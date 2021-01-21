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
  pairTheory pred_setTheory listTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf4Theory cf7Theory cf8Theory

val _ = new_theory"cf9";

Definition commit_def:
  commit c b = mk_cf (c with agent := b)
End

Definition commit_diff_def:
  commit_diff c b = mk_cf (c with agent := c.agent DIFF b)
End

Theorem commit_diff_commit:
  commit_diff c b = commit c (c.agent DIFF b)
Proof
  rw[commit_def, commit_diff_def]
QED

Theorem commit_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  commit c b ∈ chu_objects w
Proof
  rw[commit_def, in_chu_objects]
  \\ fs[wf_def, image_def, PULL_EXISTS, SUBSET_DEF, finite_cf_def]
  \\ metis_tac[SUBSET_DEF, SUBSET_FINITE]
QED

Theorem commit_diff_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  commit_diff c b ∈ chu_objects w
Proof
  rw[commit_diff_commit]
QED

Theorem commit_additive_subagent:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  additive_subagent (commit c b) c
Proof
  rw[additive_subagent_committing]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qexistsl_tac[`c.env`,`c.eval`]
  \\ simp[commit_def]
  \\ `c.world = w` by fs[in_chu_objects]
  \\ conj_tac \\ qmatch_goalsub_abbrev_tac`x ≃ y -: _`
  \\ `x ∈ chu_objects w ∧ y = x` suffices_by rw[]
  \\ simp[Abbr`x`, Abbr`y`, cf_component_equality]
  \\ fs[in_chu_objects, mk_cf_def, wf_def, finite_cf_def]
  \\ simp[image_def, SUBSET_DEF, PULL_EXISTS, FUN_EQ_THM]
  \\ metis_tac[SUBSET_DEF, SUBSET_FINITE]
QED

Theorem commit_diff_additive_subagent:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  additive_subagent (commit_diff c b) c
Proof
  rw[commit_diff_commit]
  \\ irule commit_additive_subagent
  \\ fs[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem is_brother_commit_diff:
  c ∈ chu_objects w ∧ b ⊆ c.agent ⇒
  is_brother c (commit c b) (commit_diff c b)
Proof
  rw[is_brother_def]
  \\ qexists_tac`mk_cf <| world := w;
       agent := (sum (commit c b) (commit_diff c b)).agent;
       env := IMAGE (W (CURRY encode_pair)) c.env;
       eval := sum_eval c.eval c.eval |>`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c' -: _`
  \\ `c.world = w` by fs[in_chu_objects]
  \\ `(commit_diff c b).world = w ∧ (commit c b).world = w`
  by simp[commit_diff_def, commit_def]
  \\ `c' ∈ chu_objects w`
  by (
    `sum (commit c b) (commit_diff c b) ∈ chu_objects w` by simp[]
    \\ fs[in_chu_objects, Abbr`c'`, wf_def, Excl"sum_in_chu_objects"]
    \\ fs[finite_cf_def, image_def, PULL_EXISTS, SUBSET_DEF]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[Once sum_def, EXISTS_PROD, PULL_EXISTS]
    \\ simp[Once commit_def, Once commit_diff_def]
    \\ disch_then drule \\ disch_then drule
    \\ simp[sum_def, mk_cf_def, PULL_EXISTS, commit_def, commit_diff_def]
    \\ rw[sum_eval_def] \\ rw[]
    \\ qpat_x_assum`a ∈ _` mp_tac
    \\ simp_tac(srw_ss())[sum_def, commit_def, commit_diff_def]
    \\ metis_tac[])
  \\ conj_tac
  >- (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c c' <|
         map_agent := λa. encode_sum ((if a ∈ b then INL else INR) a);
         map_env := FST o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism c' c <|
         map_agent := λa. sum_CASE (decode_sum a) I I;
         map_env := W (CURRY encode_pair) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c'`, mk_cf_def, PULL_EXISTS]
      \\ simp[sum_def, PULL_EXISTS, commit_def, commit_diff_def]
      \\ rw[sum_eval_def]
      \\ Cases_on`a ∈ b` \\ fs[])
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c'`, mk_cf_def, PULL_EXISTS]
      \\ simp[sum_def, PULL_EXISTS, commit_def, commit_diff_def]
      \\ rw[sum_eval_def] \\ rw[]
      \\ rfs[SUBSET_DEF] )
    \\ simp[homotopic_id_map_env_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[restrict_def, mk_chu_morphism_def]
    \\ rw[Abbr`c'`, mk_cf_def] \\ rw[] \\ fs[] )
  \\ simp[]
  \\ simp[is_subsum_def]
  \\ simp[Once sum_def]
  \\ conj_tac >- simp[Abbr`c'`]
  \\ conj_tac >- simp[Abbr`c'`]
  \\ conj_tac >- (
    simp[Abbr`c'`, sum_def]
    \\ simp[commit_def, commit_diff_def]
    \\ simp[SUBSET_DEF, PULL_EXISTS] )
  \\ conj_tac >- (
    simp[Abbr`c'`, restrict_def, mk_cf_def, sum_def,
         PULL_EXISTS, EXISTS_PROD, commit_def, commit_diff_def]
    \\ rw[sum_eval_def, FUN_EQ_THM]
    \\ rw[] \\ rw[] \\ gs[] )
  \\ qmatch_goalsub_abbrev_tac`commit c b ≃ c1 -: _`
  \\ qmatch_goalsub_abbrev_tac`commit_diff c b ≃ c2 -: _`
  \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
  by (
    fs[in_chu_objects, Abbr`c1`, Abbr`c2`]
    \\ fs[wf_def, finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[commit_def, commit_diff_def, sum_def, Abbr`c'`]
    \\ metis_tac[SUBSET_FINITE] )
  \\ conj_tac >- (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism (commit c b) c1 <|
         map_agent := encode_sum o INL;
         map_env := FST o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism c1 (commit c b) <|
         map_agent := OUTL o decode_sum;
         map_env := W (CURRY encode_pair) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, commit_def, mk_cf_def]
      \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
      \\ simp[sum_def, sum_eval_def, commit_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, commit_def, mk_cf_def, PULL_EXISTS]
      \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
      \\ simp[sum_def, sum_eval_def, commit_def] )
    \\ simp[homotopic_id_map_agent_id]
    \\ imp_res_tac compose_in_chu
    \\ simp[restrict_def, mk_chu_morphism_def]
    \\ simp[commit_def, mk_cf_def, PULL_EXISTS, FUN_EQ_THM, Abbr`c1`] )
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (commit_diff c b) c2 <|
       map_agent := encode_sum o INR;
       map_env := FST o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism c2 (commit_diff c b) <|
       map_agent := OUTR o decode_sum;
       map_env := W (CURRY encode_pair) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c2`, commit_diff_def, mk_cf_def]
    \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
    \\ simp[sum_def, sum_eval_def, commit_diff_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c2`, commit_diff_def, mk_cf_def, PULL_EXISTS]
    \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
    \\ simp[sum_def, sum_eval_def, commit_diff_def] )
  \\ simp[homotopic_id_map_agent_id]
  \\ imp_res_tac compose_in_chu
  \\ simp[restrict_def, mk_chu_morphism_def]
  \\ simp[commit_diff_def, mk_cf_def, PULL_EXISTS, FUN_EQ_THM, Abbr`c2`]
QED

Definition assume_def:
  assume c f = mk_cf (c with env := f)
End

Definition assume_diff_def:
  assume_diff c f = mk_cf (c with env := c.env DIFF f)
End

(* TODO: example of assume_diff for meteor example *)

Theorem swap_assume:
  swap (assume c f) = commit (swap c) f
Proof
  simp[assume_def, commit_def, cf_component_equality]
  \\ simp[mk_cf_def, FUN_EQ_THM] \\ rw[] \\ fs[]
QED

Theorem swap_assume_diff:
  swap (assume_diff c f) = commit_diff (swap c) f
Proof
  simp[assume_diff_def, commit_diff_def, cf_component_equality]
  \\ simp[mk_cf_def, FUN_EQ_THM] \\ rw[] \\ fs[]
QED

Theorem swap_commit:
  swap (commit c b) = assume (swap c) b
Proof
  metis_tac[swap_swap, swap_assume]
QED

Theorem swap_commit_diff:
  swap (commit_diff c b) = assume_diff (swap c) b
Proof
  metis_tac[swap_swap, swap_assume_diff]
QED

Theorem assume_additive_subenvironment:
  c ∈ chu_objects w ∧ f ⊆ c.env ⇒
  additive_subenvironment c (assume c f)
Proof
  rw[additive_subenvironment_def, swap_assume]
  \\ irule commit_additive_subagent
  \\ simp[] \\ metis_tac[]
QED

Theorem assume_diff_additive_subenvironment:
  c ∈ chu_objects w ∧ f ⊆ c.env ⇒
  additive_subenvironment c (assume_diff c f)
Proof
  rw[additive_subenvironment_def, swap_assume_diff]
  \\ irule commit_diff_additive_subagent
  \\ simp[] \\ metis_tac[]
QED

Definition partitions_def:
  partitions X Y ⇔ ∃R. R equiv_on Y ∧ X = partition R Y
End

Theorem partitions_thm:
  partitions X Y ⇔
  ((∀x. x ∈ X ⇒ x ≠ ∅ ∧ x ⊆ Y) ∧
   (∀y. y ∈ Y ⇒ ∃!x. x ∈ X ∧ y ∈ x))
Proof
  simp[partitions_def]
  \\ eq_tac \\ strip_tac
  >- (
    simp[partition_def]
    \\ conj_tac
    >- (
      CCONTR_TAC \\ fs[]
      \\ pop_assum mp_tac
      \\ simp[GSYM MEMBER_NOT_EMPTY, SUBSET_DEF]
      \\ metis_tac[equiv_on_def] )
    \\ rpt strip_tac
    \\ simp[EXISTS_UNIQUE_THM, PULL_EXISTS]
    \\ qexists_tac`y`
    \\ rw[]
    >- metis_tac[equiv_on_def]
    \\ metis_tac[equiv_class_eq])
  \\ fs[EXISTS_UNIQUE_ALT]
  \\ fs[Once (GSYM RIGHT_EXISTS_IMP_THM)]
  \\ fs[SKOLEM_THM]
  \\ qexists_tac`λy z. f y = f z`
  \\ simp[equiv_on_def]
  \\ conj_tac >- metis_tac[]
  \\ simp[partition_def, Once EXTENSION]
  \\ rw[EQ_IMP_THM]
  >- (
    `∃a. a ∈ x ∧ a ∈ Y` by metis_tac[MEMBER_NOT_EMPTY, SUBSET_DEF]
    \\ qexists_tac`a` \\ simp[]
    \\ `f a = x` by metis_tac[]
    \\ simp[EXTENSION]
    \\ metis_tac[SUBSET_DEF] )
  \\ `f y ∈ X ∧ y ∈ f y` by metis_tac[]
  \\ qmatch_goalsub_abbrev_tac`z ∈ X`
  \\ `z = f y` suffices_by rw[]
  \\ rw[Abbr`z`, EXTENSION]
  \\ reverse(Cases_on`x ∈ Y`) \\ simp[]
  >- metis_tac[SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem partitions_FINITE:
  partitions X Y ∧ FINITE Y ⇒
  FINITE X ∧ EVERY_FINITE X
Proof
  rw[partitions_def]
  \\ metis_tac[FINITE_partition]
QED

Definition is_repfn_def:
  is_repfn X q ⇔
  extensional q X ∧ ∀x. x ∈ X ⇒ q x ∈ x
End

Definition encode_set_def:
  encode_set = encode_list o SET_TO_LIST
End

Definition decode_set_def:
  decode_set = set o decode_list
End

Theorem decode_encode_set[simp]:
  FINITE s ⇒ decode_set (encode_set s) = s
Proof
  rw[decode_set_def, encode_set_def, SET_TO_LIST_INV]
QED

Definition repfns_def:
  repfns b =
    { encode_function (IMAGE encode_set b)
        (restrict (q o decode_set) (IMAGE encode_set b))
      | q | is_repfn b q }
End

Theorem FINITE_repfns[simp]:
  FINITE b ∧ EVERY_FINITE b ⇒ FINITE (repfns b)
Proof
  rw[repfns_def]
  \\ qspec_then`λq. IMAGE (λx. (x, (decode_function q (encode_set x)))) b` irule FINITE_INJ
  \\ qexists_tac`b`
  \\ qexists_tac`{IMAGE (λx. (x, q x)) b | q | is_repfn b q}`
  \\ conj_tac
  >- (
    irule SUBSET_FINITE
    \\ qexists_tac`POW (b × BIGUNION b)`
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ simp[IN_POW, SUBSET_DEF, PULL_EXISTS]
    \\ simp[is_repfn_def]
    \\ metis_tac[] )
  \\ simp[INJ_DEF, PULL_EXISTS]
  \\ qho_match_abbrev_tac`(∀q. is_repfn b q ⇒ ∃q'. P q q') ∧ _`
  \\ `∀q. is_repfn b q ⇒ P q q`
  by (
    simp[Abbr`P`]
    \\ qx_gen_tac`q`
    \\ strip_tac
    \\ irule IMAGE_CONG
    \\ simp[restrict_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ fs[Abbr`P`]
  \\ conj_tac >- metis_tac[]
  \\ rw[Once EXTENSION, FORALL_PROD]
  \\ AP_TERM_TAC
  \\ simp[restrict_def, PULL_EXISTS, FUN_EQ_THM]
  \\ rw[] \\ simp[]
  \\ metis_tac[]
QED

Definition external_def:
  external c b = mk_cf <| world := c.world;
    agent := repfns b;
    env := IMAGE encode_pair (IMAGE encode_set b × c.env);
    eval := λq p. c.eval
      (decode_function q (FST (decode_pair p)))
      (SND (decode_pair p)) |>
End

Definition external_mod_def:
  external_mod c b = mk_cf <| world := c.world;
    agent := IMAGE encode_set b;
    env := IMAGE encode_pair (repfns b × c.env);
    eval := λa e. c.eval (decode_function (FST (decode_pair e)) a)
                         (SND (decode_pair e)) |>
End

Theorem external_in_chu_objects:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  external c b ∈ chu_objects w
Proof
  simp[in_chu_objects, external_def]
  \\ strip_tac
  \\ fs[wf_def, finite_cf_def]
  \\ drule partitions_FINITE
  \\ rw[]
  \\ rw[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ first_x_assum irule \\ rw[]
  \\ fs[repfns_def]
  \\ simp[restrict_def]
  \\ fs[is_repfn_def, partitions_thm]
  \\ metis_tac[SUBSET_DEF]
QED

Theorem external_mod_in_chu_objects:
  c ∈ chu_objects w ∧ partitions b c.agent ⇒
  external_mod c b ∈ chu_objects w
Proof
  simp[in_chu_objects, external_mod_def]
  \\ strip_tac
  \\ fs[wf_def, finite_cf_def]
  \\ drule partitions_FINITE
  \\ rw[]
  \\ rw[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ first_x_assum irule \\ rw[]
  \\ fs[repfns_def]
  \\ simp[restrict_def]
  \\ fs[is_repfn_def, partitions_thm]
  \\ metis_tac[SUBSET_DEF]
QED

val _ = export_theory();
