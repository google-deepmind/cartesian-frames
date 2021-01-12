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

Definition comm_subsum_def:
  comm_subsum s = mk_cf
    <| world := s.world;
       agent := IMAGE comm_sum.map_agent s.agent;
       env := IMAGE comm_sum.map_env s.env;
       eval := λa e. s.eval (comm_sum.map_agent a) (comm_sum.map_env e) |>
End

Theorem comm_subsum_idem:
  wf s ∧
  s.agent ⊆ (sum c d).agent ∧
  s.env ⊆ (sum c d).env ⇒
  comm_subsum (comm_subsum s) = s
Proof
  rw[comm_subsum_def, mk_cf_def]
  \\ simp[cf_component_equality, PULL_EXISTS]
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ fs[sum_def, comm_sum_def, PULL_EXISTS, SUBSET_DEF]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ qexists_tac`x` \\ simp[])
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ simp[sum_def, comm_sum_def, PULL_EXISTS, UNCURRY]
    \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ qexists_tac`x` \\ simp[] )
  \\ simp[FUN_EQ_THM]
  \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS, EXISTS_PROD, wf_def]
  \\ rw[comm_sum_def] \\ gvs[]
  \\ res_tac \\ gvs[UNCURRY]
  \\ TRY (
    first_x_assum irule
    \\ CCONTR_TAC \\ fs[] \\ fs[]
    \\ res_tac \\ fs[]
    \\ first_x_assum(qspecl_then[`a`,`e`]mp_tac)
    \\ simp[]
    \\ NO_TAC)
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`∀x y. _`mp_tac \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
QED

Theorem comm_subsum_in_chu_objects:
  s ∈ chu_objects w ∧
  s.agent ⊆ (sum c d).agent ∧
  s.env ⊆ (sum c d).env
  ⇒ comm_subsum s ∈ chu_objects w
Proof
  rw[chu_objects_def, comm_subsum_def]
  \\ fs[wf_def, finite_cf_def]
  \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[]
  \\ fs[SUBSET_DEF, sum_def, comm_sum_def]
  \\ res_tac \\ gs[UNCURRY]
QED

Theorem comm_subsum_iso:
  s ∈ chu_objects w ∧
  s.agent ⊆ (sum c d).agent ∧
  s.env ⊆ (sum c d).env
  ⇒
  s ≅ comm_subsum s -: chu w
Proof
  rw[iso_objs_thm, chu_iso_bij]
  \\ qexists_tac`mk_chu_morphism s (comm_subsum s) comm_sum`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_tac >- metis_tac[comm_subsum_in_chu_objects]
    \\ simp[is_chu_morphism_def,mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[comm_subsum_def, PULL_EXISTS, mk_cf_def]
    \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS]
    \\ rw[]
    \\ res_tac \\ gs[comm_sum_def, UNCURRY] )
  \\ fs[maps_to_in_chu]
  \\ simp[mk_chu_morphism_def]
  \\ simp[comm_subsum_def]
  \\ simp[BIJ_IFF_INV, PULL_EXISTS]
  \\ qexistsl_tac[`comm_sum.map_agent`,`comm_sum.map_env`]
  \\ fs[SUBSET_DEF, sum_def, PULL_EXISTS]
  \\ rw[]
  \\ res_tac \\ gs[comm_sum_def, UNCURRY]
  \\ qexists_tac`x` \\ simp[]
QED

Theorem is_subsum_comm_subsum:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  is_subsum c d s ⇒ is_subsum d c (comm_subsum s)
Proof
  simp[is_subsum_def]
  \\ strip_tac
  \\ conj_tac >- simp[sum_def, UNION_COMM,comm_subsum_def]
  \\ conj_asm1_tac
  >- (
    simp[sum_def, comm_subsum_def,
         comm_sum_def, GSYM IMAGE_COMPOSE]
    \\ simp[combinTheory.o_DEF, UNION_COMM])
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS, comm_subsum_def,
       comm_sum_def, UNCURRY]
    \\ fs[sum_def]
    \\ gen_tac \\ strip_tac \\ res_tac
    \\ simp[] )
  \\ conj_tac
  >- (
    fs[comm_subsum_def]
    \\ simp[FUN_EQ_THM, restrict_def, mk_cf_def]
    \\ fs[SUBSET_DEF]
    \\ rw[]
    \\ res_tac
    \\ fs[sum_def, mk_cf_def, comm_sum_def,
          sum_eval_def, UNCURRY]
    \\ gs[] \\ rw[] \\ gs[] )
  \\ qmatch_assum_abbrev_tac`c ≃ c1 -: _`
  \\ qmatch_assum_abbrev_tac`d ≃ d1 -: _`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c2 -: _`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d2 -: _`
  \\ `c2 = comm_subsum c1`
  by (
    simp[cf_component_equality]
    \\ simp[Abbr`c2`, Abbr`c1`]
    \\ simp[comm_subsum_def, mk_cf_def]
    \\ conj_tac
    >- simp[EXTENSION, comm_sum_def, PULL_EXISTS]
    \\ simp[FUN_EQ_THM, restrict_def]
    \\ rw[] \\ gs[comm_sum_def]
    \\ `F` suffices_by rw[]
    \\ qpat_x_assum`∀x. _`mp_tac
    \\ simp[PULL_EXISTS]
    \\ dsimp[sum_def, PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ `d2 = comm_subsum d1`
  by (
    simp[cf_component_equality]
    \\ simp[Abbr`d2`, Abbr`d1`]
    \\ simp[comm_subsum_def, mk_cf_def]
    \\ conj_tac
    >- simp[EXTENSION, comm_sum_def, PULL_EXISTS]
    \\ simp[FUN_EQ_THM, restrict_def]
    \\ rw[] \\ gs[comm_sum_def]
    \\ `F` suffices_by rw[]
    \\ qpat_x_assum`∀x. _`mp_tac
    \\ simp[PULL_EXISTS]
    \\ dsimp[sum_def, PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[] )
  \\ `sum c d ∈ chu_objects w` by simp[]
  \\ `c1 ∈ chu_objects w`
  by (
    simp[chu_objects_def, Abbr`c1`]
    \\ fs[chu_objects_def, wf_def]
    \\ fs[finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[sum_def] \\ simp[] )
  \\ `d1 ∈ chu_objects w`
  by (
    simp[chu_objects_def, Abbr`d1`]
    \\ fs[chu_objects_def, wf_def]
    \\ fs[finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[sum_def] \\ simp[] )
  \\ `c.world = w ∧ d.world = w` by rfs[chu_objects_def]
  \\ conj_tac \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule iso_homotopy_equiv
  \\ rw[]
  \\ irule comm_subsum_iso
  \\ rw[]
  \\ simp[Abbr`c1`, Abbr`d1`]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[sum_def]
QED

Theorem is_subsum_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  BIJ comm_subsum (is_subsum c d) (is_subsum d c) ∧
    ∀s. is_subsum c d s ⇒ s ≅ (comm_subsum s) -: chu w
Proof
  reverse(rw[])
  >- (
    irule comm_subsum_iso
    \\ conj_tac >- metis_tac[subsum_in_chu_objects]
    \\ fs[is_subsum_def]
    \\ metis_tac[SUBSET_REFL] )
  \\ rw[BIJ_IFF_INV]
  >- (
    pop_assum mp_tac
    \\ simp[IN_DEF]
    \\ metis_tac[is_subsum_comm_subsum])
  \\ qexists_tac`comm_subsum`
  \\ conj_tac >- (
    simp[IN_DEF]
    \\ metis_tac[is_subsum_comm_subsum] )
  \\ rw[]
  \\ irule comm_subsum_idem
  \\ pop_assum mp_tac
  \\ simp[Once IN_DEF]
  \\ strip_tac
  \\ `x ∈ chu_objects w` by imp_res_tac subsum_in_chu_objects
  \\ fs[chu_objects_def]
  \\ fs[is_subsum_def]
  \\ metis_tac[SUBSET_REFL]
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
