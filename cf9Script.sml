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

open HolKernel boolLib bossLib Parse
  pairTheory pred_setTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf7Theory cf8Theory

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

val _ = export_theory();
