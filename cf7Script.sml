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
  cf0Theory cf1Theory cf2Theory cf4Theory cf5Theory cf6Theory

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
    \\ pop_assum mp_tac
    \\ qpat_x_assum`c ∈ chu_objects _ `mp_tac
    \\ rewrite_tac[chu_objects_def, wf_def]
    \\ simp[finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ ntac 2 strip_tac
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[sum_def] \\ simp[] )
  \\ `d1 ∈ chu_objects w`
  by (
    simp[chu_objects_def, Abbr`d1`]
    \\ qpat_x_assum`(sum _ _) ∈ _`mp_tac
    \\ qpat_x_assum`d ∈ chu_objects _ `mp_tac
    \\ rewrite_tac[chu_objects_def, wf_def]
    \\ simp[finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ ntac 2 strip_tac
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

Theorem comm_tensor_env_in_tensor_env:
  m ∈ (tensor c d).env ∧ c.world = d.world ⇒
  comm_tensor_env d c m ∈ (tensor d c).env
Proof
  rw[tensor_def, hom_def, maps_to_in_chu]
  \\ rw[comm_tensor_env_def]
  \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
  \\ simp[PULL_EXISTS]
  \\ qexists_tac`x.dom.world`
  \\ qmatch_goalsub_abbrev_tac`encode_morphism m`
  \\ qexists_tac`m`
  \\ conj_asm1_tac >- ( fs[maps_to_in_chu] \\ metis_tac[] )
  \\ simp[Abbr`m`]
  \\ fs[maps_to_in_chu] \\ gs[]
  \\ simp[mk_chu_morphism_def]
  \\ fs[is_chu_morphism_def]
  \\ fs[restrict_def]
QED

Theorem comm_tensor_env_idem:
  (m ∈ chu w | c → swap d |) ⇒
  comm_tensor_env c d (comm_tensor_env d c (encode_morphism m))
  = encode_morphism m
Proof
  rw[comm_tensor_env_def]
  \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
  \\ fs[hom_def]
  \\ conj_asm1_tac
  >- (
    fs[maps_to_in_chu]
    \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def] )
  \\ AP_TERM_TAC
  \\ simp[morphism_component_equality]
  \\ fs[maps_to_in_chu]
  \\ simp[chu_morphism_map_component_equality,
          mk_chu_morphism_def]
  \\ fs[is_chu_morphism_def]
  \\ fs[restrict_def, extensional_def, FUN_EQ_THM]
  \\ rw[]
QED

Definition comm_subtensor_def:
  comm_subtensor c d t = mk_cf
    <| world := t.world;
       agent := IMAGE comm_sum.map_env t.agent;
       env := IMAGE (comm_tensor_env c d) t.env;
       eval := λa e. t.eval (comm_sum.map_env a) (comm_tensor_env d c e) |>
End

Theorem comm_subtensor_idem:
  wf t ∧
  t.agent ⊆ (tensor c d).agent ∧
  t.env ⊆ (tensor c d).env ⇒
  comm_subtensor c d (comm_subtensor d c t) = t
Proof
  rw[comm_subtensor_def, mk_cf_def]
  \\ simp[cf_component_equality, PULL_EXISTS]
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ simp[sum_def, comm_sum_def, PULL_EXISTS, UNCURRY]
    \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ qexists_tac`x` \\ simp[] )
  \\ conj_tac
  >- (
    simp[EXTENSION, PULL_EXISTS]
    \\ fs[tensor_def, SUBSET_DEF]
    \\ rw[EQ_IMP_THM] \\ res_tac \\ gs[]
    \\ TRY (qexists_tac`x` \\ simp[])
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ fs[hom_def] \\ metis_tac[] )
  \\ simp[FUN_EQ_THM]
  \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS, EXISTS_PROD, wf_def]
  \\ rw[comm_sum_def] \\ gvs[]
  \\ res_tac \\ gvs[UNCURRY]
  \\ TRY (
    qpat_x_assum`_ = _`mp_tac
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ conj_tac >- metis_tac[]
    \\ disch_then(mp_tac o Q.AP_TERM`comm_tensor_env c d`)
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ conj_tac >- metis_tac[]
    \\ rw[] )
  \\ TRY (
    first_x_assum irule
    \\ CCONTR_TAC \\ fs[] \\ fs[]
    \\ res_tac \\ fs[]
    \\ first_x_assum(qspecl_then[`a`,`e`]mp_tac)
    \\ simp[]
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    \\ metis_tac[])
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`∀x y. _`mp_tac \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
  \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
  \\ metis_tac[]
QED

Theorem comm_subtensor_in_chu_objects:
  s ∈ chu_objects w ∧
  s.agent ⊆ (tensor c d).agent ∧
  s.env ⊆ (tensor c d).env
  ⇒ comm_subtensor d c s ∈ chu_objects w
Proof
  rw[chu_objects_def, comm_subtensor_def]
  \\ fs[wf_def, finite_cf_def]
  \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
  \\ rw[]
  \\ fs[SUBSET_DEF, tensor_def, comm_sum_def]
  \\ res_tac \\ gs[UNCURRY]
  \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
  \\ metis_tac[]
QED

Theorem comm_subtensor_iso:
  s ∈ chu_objects w ∧
  s.agent ⊆ (tensor c d).agent ∧
  s.env ⊆ (tensor c d).env
  ⇒
  s ≅ comm_subtensor d c s -: chu w
Proof
  rw[iso_objs_thm, chu_iso_bij]
  \\ qexists_tac`mk_chu_morphism s (comm_subtensor d c s)
      <| map_agent := comm_sum.map_env;
         map_env := comm_tensor_env c d |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ conj_tac >- metis_tac[comm_subtensor_in_chu_objects]
    \\ simp[is_chu_morphism_def,mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[comm_subtensor_def, PULL_EXISTS, mk_cf_def]
    \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS]
    \\ rw[]
    \\ res_tac \\ gs[comm_sum_def, UNCURRY]
    \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
    >- metis_tac[]
    \\ conj_tac >- metis_tac[]
    \\ AP_THM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ simp[PAIR_FST_SND_EQ])
  \\ fs[maps_to_in_chu]
  \\ simp[mk_chu_morphism_def]
  \\ simp[comm_subtensor_def]
  \\ simp[BIJ_IFF_INV, PULL_EXISTS]
  \\ qexistsl_tac[`comm_sum.map_env`,`comm_tensor_env d c`]
  \\ fs[SUBSET_DEF, tensor_def, PULL_EXISTS]
  \\ rw[]
  \\ res_tac \\ gs[comm_sum_def, UNCURRY]
  \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
  \\ simp[]
  \\ TRY(qexists_tac`x` \\ simp[] \\ NO_TAC)
  \\ metis_tac[]
QED

Theorem is_subtensor_comm_subtensor:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  is_subtensor c d s ⇒ is_subtensor d c (comm_subtensor d c s)
Proof
  simp[is_subtensor_def]
  \\ strip_tac
  \\ conj_tac >- simp[tensor_def, UNION_COMM,comm_subtensor_def]
  \\ conj_asm1_tac
  >- (
    simp[tensor_def, comm_subtensor_def,
         comm_sum_def, EXTENSION, PULL_EXISTS, EXISTS_PROD]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS, comm_subtensor_def]
    \\ rw[]
    \\ irule comm_tensor_env_in_tensor_env
    \\ fs[chu_objects_def])
  \\ conj_tac
  >- (
    fs[comm_subtensor_def]
    \\ simp[FUN_EQ_THM, restrict_def, mk_cf_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ rpt gen_tac
    \\ reverse IF_CASES_TAC
    >- (
      IF_CASES_TAC \\ simp[] \\ fs[]
      \\ `tensor d c ∈ chu_objects w` by simp[]
      \\ pop_assum mp_tac
      \\ rewrite_tac[chu_objects_def, wf_def]
      \\ simp[] \\ strip_tac
      \\ first_x_assum irule
      \\ metis_tac[] )
    \\ fs[]
    \\ res_tac
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[Once tensor_def]
    \\ strip_tac \\ gvs[]
    \\ DEP_REWRITE_TAC[comm_tensor_env_idem]
    \\ conj_tac >- rfs[chu_objects_def]
    \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ simp[hom_def]
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ qmatch_goalsub_abbrev_tac`_.eval _ m`
    \\ `c.world = w ∧ d.world = w` by rfs[chu_objects_def]
    \\ `comm_tensor_env d c m ∈ (tensor d c).env` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp_tac(srw_ss())[tensor_def, EXISTS_PROD]
    \\ simp[hom_def]
    \\ ntac 3 strip_tac
    \\ simp[mk_cf_def, EXISTS_PROD, comm_sum_def, Abbr`m`]
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ fs[]
    \\ qpat_x_assum`_ = encode_morphism _`mp_tac
    \\ simp[comm_tensor_env_def]
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism] \\ fs[]
    \\ disch_then(mp_tac o Q.AP_TERM`decode_morphism d (swap c)`)
    \\ DEP_REWRITE_TAC[decode_encode_chu_morphism]
    \\ simp[]
    \\ conj_tac
    >- (
      fs[maps_to_in_chu]
      \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
      \\ fs[restrict_def] )
    \\ strip_tac
    \\ gvs[]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ fs[maps_to_in_chu, is_chu_morphism_def] )
  \\ qmatch_assum_abbrev_tac`c ≃ c1 -: _`
  \\ qmatch_assum_abbrev_tac`d ≃ d1 -: _`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c2 -: _`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d2 -: _`
  \\ `c.world = w ∧ d.world = w` by rfs[chu_objects_def]
  \\ `tensor c d ∈ chu_objects w` by simp[]
  \\ `c1 ∈ chu_objects w`
  by (
    pop_assum mp_tac
    \\ simp_tac(srw_ss())[chu_objects_def, Abbr`c1`]
    \\ simp[chu_objects_def, wf_def]
    \\ strip_tac
    \\ qpat_x_assum`c ∈ chu_objects _`mp_tac
    \\ qpat_x_assum`d ∈ chu_objects _`mp_tac
    \\ simp[chu_objects_def, wf_def]
    \\ fs[finite_cf_def]
    \\ ntac 2 strip_tac
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[tensor_def] \\ simp[] )
  \\ `d1 ∈ chu_objects w`
  by (
    qpat_x_assum`tensor _ _ ∈ _` mp_tac
    \\ simp_tac(srw_ss())[chu_objects_def, Abbr`d1`]
    \\ simp[chu_objects_def, wf_def]
    \\ strip_tac
    \\ qpat_x_assum`c ∈ chu_objects _`mp_tac
    \\ qpat_x_assum`d ∈ chu_objects _`mp_tac
    \\ simp[chu_objects_def, wf_def]
    \\ fs[finite_cf_def]
    \\ ntac 2 strip_tac
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ reverse conj_tac >- metis_tac[SUBSET_FINITE, SUBSET_DEF]
    \\ rw[]
    \\ first_x_assum irule \\ simp[]
    \\ rewrite_tac[tensor_def] \\ simp[] )
  \\ `c2 ∈ chu_objects w`
  by (
    qpat_x_assum`c1 ∈ chu_objects _`mp_tac
    \\ simp[chu_objects_def, Abbr`c1`, Abbr`c2`]
    \\ simp[finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[comm_subtensor_def, mk_cf_def, PULL_EXISTS]
    \\ simp[restrict_def, comm_sum_def]
    \\ disch_then assume_tac
    \\ reverse conj_tac
    >- metis_tac[IMAGE_FINITE]
    \\ pop_assum kall_tac
    \\ simp[FORALL_PROD, UNCURRY, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[Once tensor_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[comm_tensor_env_idem]
    \\ gs[]
    \\ `tensor c d ∈ chu_objects w` by simp[]
    \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [chu_objects_def, wf_def]
    \\ strip_tac \\ fs[]
    \\ first_x_assum irule
    \\ simp[tensor_def] )
  \\ `d2 ∈ chu_objects w`
  by (
    qpat_x_assum`d1 ∈ chu_objects _`mp_tac
    \\ simp[chu_objects_def, Abbr`d1`, Abbr`d2`]
    \\ simp[finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ simp[comm_subtensor_def, mk_cf_def, PULL_EXISTS]
    \\ simp[restrict_def, comm_sum_def]
    \\ disch_then assume_tac
    \\ reverse conj_tac
    >- metis_tac[IMAGE_FINITE]
    \\ pop_assum kall_tac
    \\ simp[FORALL_PROD, UNCURRY, PULL_EXISTS]
    \\ rpt gen_tac \\ strip_tac
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ pop_assum kall_tac
    \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
    \\ pop_assum mp_tac
    \\ simp[Once tensor_def]
    \\ strip_tac \\ simp[]
    \\ DEP_REWRITE_TAC[comm_tensor_env_idem]
    \\ gs[]
    \\ `tensor c d ∈ chu_objects w` by simp[]
    \\ pop_assum mp_tac
    \\ simp_tac (srw_ss()) [chu_objects_def, wf_def]
    \\ strip_tac \\ fs[]
    \\ first_x_assum irule
    \\ simp[tensor_def] )
  \\ `c1 ≃ c2 -: w`
  by (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c1 c2 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env c d (SND (decode_pair p))) |>`
    \\ qexists_tac`mk_chu_morphism c2 c1 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env d c (SND (decode_pair p))) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, Abbr`c2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ conj_asm1_tac
      >- (
        rw[]
        \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
        \\ fs[Once tensor_def]
        \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
        \\ fs[] \\ metis_tac[] )
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ rw[]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c1`, Abbr`c2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ fs[SUBSET_DEF] \\ res_tac
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[Once tensor_def]
      \\ strip_tac \\ simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
      \\ fs[]
      \\ metis_tac[] )
    \\ qmatch_goalsub_abbrev_tac`homotopic _ (f o g -: _) _`
    \\ `f o g -: chu w :- c1 → c1 -: chu w` by (
      irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ `g o f -: chu w :- c2 → c2 -: chu w` by (
      irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ conj_tac
    \\ irule homotopic_id
    \\ fs[maps_to_in_chu, pre_chu_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ DEP_REWRITE_TAC[chu_comp]
    \\ simp[pre_chu_def]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def, restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`c1`, Abbr`c2`] )
  \\ `d1 ≃ d2 -: w`
  by (
    simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism d1 d2 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env c d (SND (decode_pair p))) |>`
    \\ qexists_tac`mk_chu_morphism d2 d1 <| map_agent := I;
         map_env := λp. encode_pair (FST (decode_pair p),
           comm_tensor_env d c (SND (decode_pair p))) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`d1`, Abbr`d2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ conj_asm1_tac
      >- (
        rw[]
        \\ `x ∈ (tensor c d).env` by fs[SUBSET_DEF]
        \\ fs[Once tensor_def]
        \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
        \\ fs[] \\ metis_tac[] )
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ rw[]
      \\ `F` suffices_by rw[]
      \\ pop_assum mp_tac
      \\ simp[tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ metis_tac[] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`d1`, Abbr`d2`, PULL_EXISTS, EXISTS_PROD]
      \\ simp[mk_cf_def, restrict_def]
      \\ simp[comm_subtensor_def, PULL_EXISTS]
      \\ rpt gen_tac \\ strip_tac
      \\ simp[mk_cf_def, PULL_EXISTS, restrict_def, comm_sum_def]
      \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ pop_assum kall_tac
      \\ fs[SUBSET_DEF] \\ res_tac
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[Once tensor_def]
      \\ strip_tac \\ simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`w`comm_tensor_env_idem]
      \\ fs[]
      \\ metis_tac[] )
    \\ qmatch_goalsub_abbrev_tac`homotopic _ (f o g -: _) _`
    \\ `f o g -: chu w :- d1 → d1 -: chu w` by (
      irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ `g o f -: chu w :- d2 → d2 -: chu w` by (
      irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ conj_tac
    \\ irule homotopic_id
    \\ fs[maps_to_in_chu, pre_chu_def]
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ DEP_REWRITE_TAC[chu_comp]
    \\ simp[pre_chu_def]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def, restrict_def, FUN_EQ_THM]
    \\ simp[Abbr`d1`, Abbr`d2`] )
  \\ metis_tac[homotopy_equiv_trans]
QED

Theorem is_subtensor_comm:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  BIJ (comm_subtensor d c) (is_subtensor c d) (is_subtensor d c) ∧
  ∀t. is_subtensor c d t ⇒ t ≅ comm_subtensor d c t -: chu w
Proof
  reverse(rw[])
  >- (
    irule comm_subtensor_iso
    \\ conj_tac >- metis_tac[subtensor_in_chu_objects]
    \\ fs[is_subtensor_def])
  \\ rw[BIJ_IFF_INV]
  >- (
    pop_assum mp_tac
    \\ simp[IN_DEF]
    \\ metis_tac[is_subtensor_comm_subtensor])
  \\ qexists_tac`comm_subtensor c d`
  \\ conj_tac >- (
    simp[IN_DEF]
    \\ metis_tac[is_subtensor_comm_subtensor] )
  \\ rw[]
  \\ irule comm_subtensor_idem
  \\ pop_assum mp_tac
  \\ simp[Once IN_DEF]
  \\ strip_tac
  \\ `x ∈ chu_objects w` by imp_res_tac subtensor_in_chu_objects
  \\ fs[chu_objects_def]
  \\ fs[is_subtensor_def]
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

Theorem subsum_subagent:
  c1 ∈ chu_objects w ∧
  c2 ∈ chu_objects w ∧
  is_subsum c1 c2 d ⇒
  c1 ◁ d -: w ∧ c2 ◁ d -: w
Proof
  qho_match_abbrev_tac`P c1 c2 d ⇒ Q c1 c2 d`
  \\ `∀c1 c2 d. P c1 c2 d ⇒ Q c1 c1 d`
  suffices_by (
    simp[Abbr`P`, Abbr`Q`]
    \\ ntac 2 strip_tac
    \\ conj_tac >- metis_tac[]
    \\ `is_subsum c2 c1 (comm_subsum d)`
    by metis_tac[is_subsum_comm_subsum]
    \\ irule subagent_homotopy_equiv
    \\ qexistsl_tac[`c2`,`comm_subsum d`]
    \\ simp[]
    \\ conj_tac
    >- (
      simp[Once homotopy_equiv_sym]
      \\ irule iso_homotopy_equiv
      \\ metis_tac[is_subsum_comm] )
    \\ metis_tac[] )
  \\ simp[Abbr`P`, Abbr`Q`]
  \\ rpt gen_tac \\ strip_tac
  \\ `d ∈ chu_objects w` by metis_tac[subsum_in_chu_objects]
  \\ simp[subagent_currying]
  \\ simp[currying_subagent_def]
  \\ `c1.world = w ∧ c2.world = w` by rfs[chu_objects_def]
  \\ gs[is_subsum_def]
  \\ qmatch_assum_abbrev_tac`c1 ≃ b1 -: _`
  \\ qexists_tac`mk_cf <| world := d.agent; agent := b1.agent;
       env := {""}; eval := K |>`
  \\ qmatch_goalsub_abbrev_tac`c1 ≃ move d b2 -: _`
  \\ `b1 ∈ chu_objects w`
  by (
    qpat_x_assum`d ∈ _`mp_tac
    \\ fs[chu_objects_def, Abbr`b1`]
    \\ fs[wf_def, finite_cf_def]
    \\ fs[SUBSET_DEF, image_def, PULL_EXISTS, restrict_def]
    \\ `(sum c1 c2).world = w` by simp[sum_def]
    \\ rw[]
    \\ first_x_assum irule
    \\ simp[Once sum_def] )
  \\ `b2 ∈ chu_objects d.agent`
  by (
    simp[chu_objects_def, Abbr`b2`]
    \\ simp[SUBSET_DEF, image_def]
    \\ conj_tac >- (
      simp[Abbr`b1`, PULL_EXISTS] \\ simp[sum_def] )
    \\ simp[finite_cf_def, Abbr`b1`]
    \\ `wf c1 ∧ wf (sum c1 c2)` by rfs[chu_objects_def]
    \\ `finite_cf c1 ∧ finite_cf (sum c1 c2)` by fs[wf_def]
    \\ fs[finite_cf_def] )
  \\ `move d b2 ∈ chu_objects w`
  by ( irule move_in_chu_objects \\ simp[] )
  \\ `b1 ≃ move d b2 -: w`
  suffices_by metis_tac[homotopy_equiv_trans]
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism b1 (move d b2) <| map_agent := I;
       map_env := SND o decode_pair |>`
  \\ qexists_tac`mk_chu_morphism (move d b2) b1 <| map_agent := I;
       map_env := λe. encode_pair ("", e) |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[Abbr`b2`, move_def, Abbr`b1`, PULL_EXISTS]
    \\ simp[mk_cf_def, restrict_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def, PULL_EXISTS]
    \\ simp[restrict_def]
    \\ simp[Abbr`b2`, move_def, Abbr`b1`, PULL_EXISTS]
    \\ simp[mk_cf_def, restrict_def] )
  \\ qmatch_goalsub_abbrev_tac`homotopic w (f o g -: _) _`
  \\ `f o g -: chu w :- b1 → b1 -: chu w` by (
    irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ `g o f -: chu w :- move d b2 → move d b2 -: chu w` by (
    irule maps_to_comp \\ simp[] \\ metis_tac[] )
  \\ conj_tac
  \\ irule homotopic_id
  \\ fs[maps_to_in_chu, pre_chu_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ DEP_REWRITE_TAC[chu_comp]
  \\ simp[pre_chu_def]
  \\ simp[composable_in_def, pre_chu_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def, restrict_def, FUN_EQ_THM]
  \\ simp[Abbr`b1`, Abbr`b2`]
QED

val _ = export_theory();
