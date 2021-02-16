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
  pred_setTheory listTheory sortingTheory
  cf0Theory ex0Theory cf1Theory cf2Theory cf9Theory cfaTheory

val _ = new_theory"exa";

Definition rs_def:
  rs = {{"ur";"nr"};{"us";"ns"}}
End

Theorem partitions_rs:
  partitions rs runs_cf1.world
Proof
  rw[partitions_thm, rs_def, runs_cf1_def]
  \\ rw[SUBSET_DEF, EXISTS_UNIQUE_THM]
  \\ gs[] \\ dsimp[]
QED

Theorem rs_in_obs_part_runs_cf2:
  rs ∈ obs_part runs_cf2
Proof
  rw[obs_part_def, partitions_rs]
  \\ rw[runs2_obs, union_closure_def]
  \\ fs[rs_def, SUBSET_DEF]
  \\ metis_tac[BIGUNION_SING, IN_SING]
QED

Theorem runs_cf2_eval:
  runs_cf2.eval a e =
  if a ∈ runs_cf2.agent ∧ e ∈ runs_cf2.env then
    (if LENGTH a < 2 then EL 0 a else
       if EL 0 e = EL 0 a then EL 1 a else EL 2 a)
    :: e
  else ARB
Proof
  rw[runs_cf2_def, mk_cf_def]
QED

Theorem rs_in_obs_part_conditional_policies_runs_cf2:
  rs ∈ obs_part runs_cf2
Proof
  DEP_REWRITE_TAC[Q.SPEC`runs_cf1.world`(Q.GEN`w`obs_part_conditional_policies)]
  \\ conj_asm1_tac
  >- (simp[in_chu_objects] \\ EVAL_TAC)
  \\ conj_asm1_tac >- rw[partitions_rs]
  \\ rw[]
  \\ qpat_x_assum`_ ⊆ _`mp_tac
  \\ simp[Once rs_def]
  \\ strip_tac
  \\ qmatch_assum_abbrev_tac`f s ∈ _`
  \\ ntac 2 (pop_assum mp_tac)
  \\ qmatch_assum_abbrev_tac`f r ∈ _`
  \\ ntac 2 strip_tac
  \\ qexists_tac`
    if f r = "u" ∧ f s = "u" then "u" else
    if f r = "u" ∧ f s = "n" then "run" else
    if f r = "u" ∧ f s = "run" then "run" else
    if f r = "u" ∧ f s = "sun" then "u" else
    if f r = "n" ∧ f s = "u" then "sun" else
    if f r = "n" ∧ f s = "n" then "n" else
    if f r = "n" ∧ f s = "run" then "n" else
    if f r = "n" ∧ f s = "sun" then "sun" else
    if f r = "run" ∧ f s = "u" then "u" else
    if f r = "run" ∧ f s = "n" then "run" else
    if f r = "run" ∧ f s = "run" then "run" else
    if f r = "run" ∧ f s = "sun" then "u" else
    if f r = "sun" ∧ f s = "u" then "sun" else
    if f r = "sun" ∧ f s = "n" then "n" else
    if f r = "sun" ∧ f s = "run" then "n" else
    if f r = "sun" ∧ f s = "sun" then "sun" else ARB`
  \\ qmatch_goalsub_abbrev_tac`af ∈ _`
  \\ conj_asm1_tac
  >- ( fs[runs_cf2_def] \\ simp[Abbr`af`] )
  \\ rpt strip_tac
  \\ SELECT_ELIM_TAC
  \\ conj_tac >- metis_tac[in_chu_objects, partitions_thm, wf_def]
  \\ simp[rs_def]
  \\ dsimp[runs_cf2_eval]
  \\ qpat_x_assum`f _ ∈ _`mp_tac
  \\ qpat_x_assum`f _ ∈ _`mp_tac
  \\ simp[runs_cf2_def]
  \\ strip_tac \\ gs[]
  \\ strip_tac \\ gs[]
  \\ rw[Abbr`af`]
  \\ rw[Abbr`r`,Abbr`s`]
  \\ strip_tac \\ fs[runs_cf2_def]
QED

Theorem runs_cf2_as_product:
  runs_cf2 ≃ assume {"ur";"nr"} runs_cf2 && assume {"us";"ns"} runs_cf2
  -: runs_cf1.world
Proof
  mp_tac rs_in_obs_part_runs_cf2
  \\ `runs_cf2 ∈ chu_objects runs_cf1.world`
  by simp[in_chu_objects]
  \\ imp_res_tac in_chu_objects_finite_world
  \\ drule obs_part_assuming
  \\ impl_tac >- EVAL_TAC
  \\ disch_then SUBST_ALL_TAC
  \\ simp[obs_part_assuming_def]
  \\ strip_tac
  \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qmatch_goalsub_abbrev_tac`assume r _ && assume s _`
  \\ qmatch_goalsub_abbrev_tac`FOLDL prod t (MAP f _)`
  \\ irule homotopy_equiv_trans
  \\ rw[rs_def]
  \\ qexists_tac`FOLDL prod t (MAP f [r; s])`
  \\ conj_tac
  >- (
    irule FOLDL_PERM_equiv
    \\ rpt (conj_tac >- simp[])
    \\ conj_tac >- simp[EVERY_MAP, Abbr`f`]
    \\ conj_tac
    >- (
      irule PERM_MAP
      \\ irule PERM_ALL_DISTINCT
      \\ simp[]
      \\ simp[Abbr`r`, Abbr`s`, EXTENSION]
      \\ qexists_tac`"ur"` \\ simp[])
    \\ simp[Abbr`t`])
  \\ simp[]
  \\ irule homotopy_equiv_prod
  \\ simp[Abbr`f`, Abbr`t`]
  \\ irule iso_homotopy_equiv
  \\ metis_tac[prod_cfT, assume_in_chu_objects]
QED

Theorem runs_cf2_as_product_of_tensors:
  let w = runs_cf1.world in
  runs_cf2 ≃ tensor (cf1 w {"ur";"nr"}) runs_cf2 &&
             tensor (cf1 w {"us";"ns"}) runs_cf2 -: w
Proof
  rw[]
  \\ irule homotopy_equiv_trans
  \\ goal_assum(C (mp_then Any mp_tac) runs_cf2_as_product)
  \\ irule homotopy_equiv_prod
  \\ `runs_cf2 ∈ chu_objects runs_cf1.world` by simp[in_chu_objects]
  \\ imp_res_tac in_chu_objects_finite_world
  \\ `{"ur";"nr"} ⊆ runs_cf1.world` by EVAL_TAC
  \\ `{"us";"ns"} ⊆ runs_cf1.world` by EVAL_TAC
  \\ simp[]
  \\ metis_tac[assume_tensor_cf1, iso_homotopy_equiv]
QED

val _ = export_theory();
