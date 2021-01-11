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

open HolKernel boolLib bossLib Parse dep_rewrite
  pairTheory pred_setTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf6Theory

val _ = new_theory"cf7";

Definition is_subsum_def:
  is_subsum c d s ⇔
    s.world = (sum c d).world ∧
    s.agent = (sum c d).agent ∧
    s.env ⊆ (sum c d).env ∧
    (∀a. s.eval a = restrict ((sum c d).eval a) s.env) ∧
    c ≃ (mk_cf <| world := c.world;
                  agent := IMAGE (encode_sum o INL) c.agent;
                  env := s.env;
                  eval := s.eval |>) -: c.world ∧
    d ≃ (mk_cf <| world := d.world;
                  agent := IMAGE (encode_sum o INR) d.agent;
                  env := s.env;
                  eval := s.eval |>) -: d.world
End

Definition is_subtensor_def:
  is_subtensor c d t ⇔
    t.world = (tensor c d).world ∧
    t.agent = (tensor c d).agent ∧
    t.env ⊆ (tensor c d).env ∧
    (∀a. t.eval a = restrict ((tensor c d).eval a) t.env) ∧
    c ≃ (mk_cf <| world := c.world;
                  agent := c.agent;
                  env := IMAGE encode_pair (d.agent × t.env);
                  eval := λa e.
                    t.eval (encode_pair (a, FST (decode_pair e)))
                           (SND (decode_pair e)) |>) -: c.world ∧
    d ≃ (mk_cf <| world := d.world;
                  agent := d.agent;
                  env := IMAGE encode_pair (c.agent × t.env);
                  eval := λa e.
                    t.eval (encode_pair (FST (decode_pair e), a))
                           (SND (decode_pair e)) |>) -: d.world
End

Theorem finite_subsum:
  finite_cf c ∧ finite_cf d ∧ is_subsum c d s ⇒ finite_cf s
Proof
  rw[is_subsum_def]
  \\ `finite_cf (sum c d)` by imp_res_tac finite_sum
  \\ fs[finite_cf_def]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem wf_subsum:
  wf c ∧ wf d ∧ is_subsum c d s ⇒ wf s
Proof
  strip_tac
  \\ `wf (sum c d)` by imp_res_tac wf_sum
  \\ fs[wf_def]
  \\ mp_tac finite_subsum \\ simp[] \\ strip_tac
  \\ fs[is_subsum_def]
  \\ simp[restrict_def]
  \\ gs[SUBSET_DEF]
  \\ rw[]
QED

Theorem finite_subtensor:
  finite_cf c ∧ finite_cf d ∧ is_subtensor c d s ⇒ finite_cf s
Proof
  rw[is_subtensor_def]
  \\ `finite_cf (tensor c d)` by imp_res_tac finite_tensor
  \\ fs[finite_cf_def]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem wf_subtensor:
  wf c ∧ wf d ∧ is_subtensor c d s ⇒ wf s
Proof
  strip_tac
  \\ `wf (tensor c d)` by imp_res_tac wf_tensor
  \\ fs[wf_def]
  \\ mp_tac finite_subtensor \\ simp[] \\ strip_tac
  \\ fs[is_subtensor_def]
  \\ simp[restrict_def]
  \\ gs[SUBSET_DEF]
  \\ rw[]
QED

Theorem subsum_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧ is_subsum c d s ⇒
  s ∈ chu_objects w
Proof
  rw[chu_objects_def]
  >- metis_tac[wf_subsum]
  \\ fs[is_subsum_def] \\ simp[sum_def]
QED

Theorem subtensor_in_chu_objects[simp]:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧ is_subtensor c d t ⇒
  t ∈ chu_objects w
Proof
  rw[chu_objects_def]
  >- metis_tac[wf_subtensor]
  \\ fs[is_subtensor_def] \\ simp[tensor_def]
QED

Theorem sum_is_subsum:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  c.env ≠ ∅ ∧ d.env ≠ ∅
  ⇒
  is_subsum c d (sum c d)
Proof
  simp[is_subsum_def, restrict_def]
  \\ strip_tac
  \\ conj_tac
  >- (
    `sum c d ∈ chu_objects w` by simp[]
    \\ fs[chu_objects_def]
    \\ fs[wf_def, FUN_EQ_THM] \\ rw[] )
  \\ qmatch_goalsub_abbrev_tac`c ≃ c' -: _`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d' -: _`
  \\ `is_chu_morphism c c' (mk_chu_morphism c c'
        <| map_agent := encode_sum o INL;
           map_env := FST o decode_pair |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[sum_eval_def])
  \\ `is_chu_morphism d d' (mk_chu_morphism d d'
        <| map_agent := encode_sum o INR;
           map_env := SND o decode_pair |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[sum_eval_def])
  \\ qmatch_assum_abbrev_tac`is_chu_morphism c c' f.map`
  \\ qmatch_assum_abbrev_tac`is_chu_morphism d d' g.map`
  \\ `c' ∈ chu_objects w ∧ d' ∈ chu_objects w`
  by (
    simp[Abbr`c'`, Abbr`d'`]
    \\ `sum c d ∈ chu_objects w` by simp[]
    \\ fs[chu_objects_def]
    \\ fs[wf_def, finite_cf_def]
    \\ fs[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ fs[sum_def] )
  \\ `f :- c → c' -: chu w ∧ g :- d → d' -: chu w`
  by ( simp[maps_to_in_chu] \\ simp[Abbr`f`, Abbr`g`] )
  \\ `is_chu_morphism c' c (mk_chu_morphism c' c
        <| map_agent := OUTL o decode_sum;
           map_env := λe. encode_pair (e, CHOICE d.env) |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[CHOICE_DEF]
    \\ simp[sum_eval_def])
  \\ `is_chu_morphism d' d (mk_chu_morphism d' d
        <| map_agent := OUTR o decode_sum;
           map_env := λe. encode_pair (CHOICE c.env, e) |>).map`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, mk_cf_def]
    \\ simp[sum_def, PULL_EXISTS, FORALL_PROD, mk_cf_def]
    \\ simp[CHOICE_DEF]
    \\ simp[sum_eval_def])
  \\ qmatch_assum_abbrev_tac`is_chu_morphism c' c f'.map`
  \\ qmatch_assum_abbrev_tac`is_chu_morphism d' d g'.map`
  \\ `f' :- c' → c -: chu w ∧ g' :- d' → d -: chu w`
  by ( simp[maps_to_in_chu] \\ simp[Abbr`f'`, Abbr`g'`] )
  \\ `f' o f -: chu w :- c → c -: chu w`
  by ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ `g' o g -: chu w :- d → d -: chu w`
  by ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ `f o f' -: chu w :- c' → c' -: chu w`
  by ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ `g o g' -: chu w :- d' → d' -: chu w`
  by ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ `homotopic w (f' o f -: chu w) (id c -: chu w)`
  by (
    irule homotopic_id
    \\ fs[maps_to_in_chu, pre_chu_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[Abbr`f`, Abbr`f'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`c'`] )
  \\ `homotopic w (g' o g -: chu w) (id d -: chu w)`
  by (
    irule homotopic_id
    \\ fs[maps_to_in_chu, pre_chu_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[Abbr`g`, Abbr`g'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`d'`] )
  \\ `homotopic w (f o f' -: chu w) (id c' -: chu w)`
  by (
    irule homotopic_id
    \\ fs[maps_to_in_chu, pre_chu_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[Abbr`f`, Abbr`f'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`c'`]
    \\ disj2_tac \\ rw[] \\ rw[] \\ fs[])
  \\ `homotopic w (g o g' -: chu w) (id d' -: chu w)`
  by (
    irule homotopic_id
    \\ fs[maps_to_in_chu, pre_chu_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[Abbr`g`, Abbr`g'`, mk_chu_morphism_def]
    \\ simp[restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`d'`]
    \\ disj2_tac \\ rw[] \\ rw[] \\ fs[])
  \\ simp[homotopy_equiv_def]
  \\ fs[chu_objects_def]
  \\ metis_tac[]
QED

val _ = export_theory();
