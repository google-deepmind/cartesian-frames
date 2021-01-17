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
  cf0Theory cf1Theory cf2Theory cf5Theory cf6Theory cf7Theory

val _ = new_theory"cf8";

Definition additive_subagent_def:
  additive_subagent c d ⇔
    ∃c' d'.
      c'.world = c.world ∧
      d' ≃ d -: c.world ∧
      is_subsum c c' d'
End

Definition multiplicative_subagent_def:
  multiplicative_subagent c d ⇔
  ∃c' d'.
    c'.world = c.world ∧
    d' ≃ d -: c.world ∧
    is_subtensor c c' d'
End

Definition is_brother_def:
  is_brother d c c' ⇔
    ∃d'. d ≃ d' -: c.world ∧ is_subsum c c' d' ∧
         c'.world = c.world
End

Definition is_sister_def:
  is_sister d c c' ⇔
    ∃d'. d ≃ d' -: c.world ∧ is_subtensor c c' d' ∧
         c'.world = c.world
End

Theorem brother_in_chu_objects:
  is_brother d c c' ⇒
    d ∈ chu_objects c.world ∧
    c ∈ chu_objects c.world ∧
    c' ∈ chu_objects c.world
Proof
  simp[is_brother_def]
  \\ strip_tac
  \\ conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ full_simp_tac std_ss [is_subsum_def]
  \\ metis_tac[homotopy_equiv_def, maps_to_in_chu]
QED

Theorem is_brother_homotopy_equiv:
  is_brother d c c' ∧
  d1 ≃ d -: w ∧ c1 ≃ c -: w ∧ c1' ≃ c' -: w ⇒
  is_brother d1 c1 c1'
Proof
  strip_tac
  \\ imp_res_tac brother_in_chu_objects
  \\ fs[is_brother_def]
  \\ `c.world = w` by (
    `c ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [chu_objects_def]
    \\ simp[] )
  \\ first_assum(mp_then(Pat`is_subsum`)mp_tac subsum_homotopy_equiv)
  \\ disch_then drule \\ simp[]
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then(qx_choose_then`z`strip_assume_tac)
  \\ qexists_tac`z` \\ simp[]
  \\ `c1 ∈ chu_objects w ∧ c1' ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ rpt(qpat_x_assum`_ ∈ chu_objects _`mp_tac)
  \\ simp_tac std_ss [chu_objects_def] \\ simp[]
  \\ metis_tac[homotopy_equiv_trans, homotopy_equiv_sym]
QED

Theorem additive_subagent_brother:
  additive_subagent c d ⇔ ∃c'. is_brother d c c'
Proof
  metis_tac[additive_subagent_def, is_brother_def, homotopy_equiv_sym]
QED

Theorem multiplicative_subagent_sister:
  multiplicative_subagent c d ⇔ ∃c'. is_sister d c c'
Proof
  metis_tac[multiplicative_subagent_def, is_sister_def, homotopy_equiv_sym]
QED

Theorem additive_subagent_committing:
  additive_subagent c d ⇔
  ∃x y z f.
    x ⊆ y ∧
    c ≃ mk_cf <| world := c.world;
                 agent := x; env := z; eval := f |> -: c.world ∧
    d ≃ mk_cf <| world := c.world;
                 agent := y; env := z; eval := f |> -: c.world
Proof
  eq_tac
  >- (
    simp[additive_subagent_brother]
    \\ rw[is_brother_def]
    \\ qexists_tac`IMAGE (encode_sum o INL) c.agent`
    \\ qexists_tac`d'.agent`
    \\ qexists_tac`d'.env`
    \\ qexists_tac`d'.eval`
    \\ fs[is_subsum_def]
    \\ simp[SUBSET_DEF, PULL_EXISTS, Once sum_def]
    \\ qmatch_goalsub_abbrev_tac`d ≃ d'' -: _`
    \\ `d'' = d'` suffices_by rw[]
    \\ simp[cf_component_equality, Abbr`d''`, mk_cf_def]
    \\ simp[FUN_EQ_THM]
    \\ `d' ∈ chu_objects c.world`
    by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ fs[chu_objects_def]
    \\ gs[wf_def]
    \\ fs[restrict_def]
    \\ metis_tac[] )
  \\ strip_tac
  \\ simp[additive_subagent_brother]
  \\ qmatch_assum_abbrev_tac`c ≃ c1 -: _`
  \\ `∃c'. is_brother d c1 c'` suffices_by (
    strip_tac
    \\ drule is_brother_homotopy_equiv
    \\ disch_then(qspecl_then[`c.world`,`d`]mp_tac)
    \\ `d ∈ chu_objects c.world` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ simp[]
    \\ disch_then drule
    \\ imp_res_tac brother_in_chu_objects
    \\ `c1.world = c.world` by simp[Abbr`c1`]
    \\ metis_tac[homotopy_equiv_refl] )
  \\ qexists_tac`mk_cf <| world := c.world;
       agent := y DIFF x; env := z; eval := f |>`
  \\ qmatch_goalsub_abbrev_tac`is_brother d c1 c2`
  \\ simp[is_brother_def]
  \\ `c1.world = c.world ∧ c2.world = c.world` by simp[Abbr`c1`, Abbr`c2`]
  \\ gs[]
  \\ qexists_tac`mk_cf <| world := c.world;
       agent := (sum c1 c2).agent;
       env := IMAGE (λz. encode_pair (z, z)) z;
       eval := λa e. f (sum_CASE (decode_sum a) I I)
                       (FST (decode_pair e)) |>`
  \\ qmatch_goalsub_abbrev_tac`is_subsum c1 c2 s`
  \\ qmatch_assum_abbrev_tac`d ≃ d' -: _`
  \\ `c1 ∈ chu_objects c.world ∧ d' ∈ chu_objects c.world ∧
      c2 ∈ chu_objects c.world`
  by (
    conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ pop_assum mp_tac
    \\ simp[Abbr`d'`, Abbr`c2`, chu_objects_def]
    \\ simp[SUBSET_DEF, image_def, finite_cf_def, PULL_EXISTS] )
  \\ reverse conj_tac
  >- (
    simp[is_subsum_def]
    \\ conj_asm1_tac >- simp[sum_def, Abbr`s`]
    \\ conj_asm1_tac >- simp[Abbr`s`]
    \\ conj_asm1_tac
    >- (
      simp[Abbr`s`, sum_def, SUBSET_DEF, EXISTS_PROD, PULL_EXISTS]
      \\ simp[Abbr`c1`, Abbr`c2`])
    \\ conj_asm1_tac
    >- (
      simp[Abbr`s`,mk_cf_def,restrict_def,PULL_EXISTS]
      \\ gen_tac
      \\ simp[FUN_EQ_THM]
      \\ reverse(Cases_on`a ∈ (sum c1 c2).agent`) \\ simp[]
      >- (
        pop_assum mp_tac
        \\ rw[sum_def, mk_cf_def]
        \\ metis_tac[] )
      \\ gen_tac
      \\ IF_CASES_TAC \\ simp[]
      \\ fs[]
      \\ qpat_x_assum`a ∈ _`mp_tac
      \\ simp_tac(srw_ss())[sum_def, mk_cf_def]
      \\ simp[Abbr`c1`, Abbr`c2`, mk_cf_def]
      \\ rw[sum_eval_def] \\ simp[] )
    \\ qmatch_goalsub_abbrev_tac`c1 ≃ d1 -: _`
    \\ qmatch_goalsub_abbrev_tac`c2 ≃ d2 -: _`
    \\ `d1 ∈ chu_objects c.world ∧ d2 ∈ chu_objects c.world`
    by (
      `finite_cf d1 ∧ finite_cf d2`
      by (
        `finite_cf c1 ∧ finite_cf c2`
        by (
          ntac 3 (qpat_x_assum`_ ∈ _`mp_tac)
          \\ simp_tac(srw_ss())[chu_objects_def]
          \\ simp[wf_def] )
        \\ `finite_cf (sum c1 c2)` by metis_tac[finite_sum]
        \\ ntac 3 (pop_assum mp_tac)
        \\ simp[Abbr`d1`, Abbr`d2`, finite_cf_def, Excl"finite_sum"]
        \\ metis_tac[SUBSET_FINITE] )
      \\ `wf c1 ∧ wf c2` by fs[chu_objects_def]
      \\ `wf (sum c1 c2)` by simp[]
      \\ simp[chu_objects_def, Abbr`d1`, Abbr`d2`]
      \\ fs[finite_cf_def]
      \\ simp[SUBSET_DEF, image_def, PULL_EXISTS]
      \\ simp[restrict_def]
      \\ pop_assum mp_tac
      \\ simp_tac(srw_ss())[wf_def]
      \\ `(sum c1 c2).world = c.world` by simp[sum_def]
      \\ pop_assum SUBST_ALL_TAC
      \\ strip_tac
      \\ rw[] \\ first_x_assum irule
      \\ simp[Once sum_def]
      \\ metis_tac[SUBSET_DEF] )
    \\ conj_tac
    >- (
      simp[homotopy_equiv_def]
      \\ qexists_tac`mk_chu_morphism c1 d1
           <| map_agent := encode_sum o INL;
              map_env := FST o decode_pair |>`
      \\ qexists_tac`mk_chu_morphism d1 c1
           <| map_agent := OUTL o decode_sum;
              map_env :=  W (CURRY encode_pair) |>`
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu]
        \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
        \\ simp[restrict_def]
        \\ `d1.agent = IMAGE (encode_sum o INL) c1.agent` by simp[Abbr`d1`]
        \\ `d1.env = s.env` by simp[Abbr`d1`]
        \\ simp[]
        \\ `s.env = IMAGE (W (CURRY encode_pair)) c1.env`
        by ( simp[Abbr`s`, Abbr`c1`, combinTheory.W_DEF] )
        \\ simp[PULL_EXISTS]
        \\ simp[Abbr`d1`, mk_cf_def, restrict_def]
        \\ simp[sum_def, mk_cf_def]
        \\ `c2.env = c1.env` by simp[Abbr`c2`, Abbr`c1`]
        \\ simp[sum_eval_def] )
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu]
        \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
        \\ simp[restrict_def]
        \\ `d1.agent = IMAGE (encode_sum o INL) c1.agent` by simp[Abbr`d1`]
        \\ `d1.env = s.env` by simp[Abbr`d1`]
        \\ simp[PULL_EXISTS]
        \\ `s.env = IMAGE (W (CURRY encode_pair)) c1.env`
        by ( simp[Abbr`s`, Abbr`c1`, combinTheory.W_DEF] )
        \\ simp[PULL_EXISTS]
        \\ simp[Abbr`d1`, mk_cf_def, restrict_def]
        \\ simp[sum_def, mk_cf_def]
        \\ `c2.env = c1.env` by simp[Abbr`c2`, Abbr`c1`]
        \\ simp[sum_eval_def] )
      \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
      \\ imp_res_tac maps_to_comp \\ fs[]
      \\ conj_tac \\ irule homotopic_id
      \\ (conj_tac >- metis_tac[maps_to_in_chu])
      \\ (conj_tac >- metis_tac[maps_to_in_chu])
      \\ simp_tac (srw_ss()) [pre_chu_def]
      \\ (conj_tac >- metis_tac[maps_to_in_chu])
      \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
      \\ (conj_tac
      >- (
        simp[composable_in_def]
        \\ simp_tac (srw_ss()) [pre_chu_def]
        \\ metis_tac[maps_to_in_chu] ))
      \\ simp[pre_chu_def, restrict_def]
      \\ simp[Abbr`j`, Abbr`k`, restrict_def]
      \\ simp[mk_chu_morphism_def, restrict_def]
      \\ simp[Abbr`d1`]
      \\ simp[FUN_EQ_THM]
      \\ simp[Abbr`s`, PULL_EXISTS]
      \\ disj1_tac
      \\ rw[] \\ rw[] \\ fs[] \\ fs[Abbr`c1`] )
    \\ simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c2 d2
         <| map_agent := encode_sum o INR;
            map_env := FST o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism d2 c2
         <| map_agent := OUTR o decode_sum;
            map_env :=  W (CURRY encode_pair) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ `d2.agent = IMAGE (encode_sum o INR) c2.agent` by simp[Abbr`d2`]
      \\ `d2.env = s.env` by simp[Abbr`d2`]
      \\ simp[]
      \\ `s.env = IMAGE (W (CURRY encode_pair)) c2.env`
      by ( simp[Abbr`s`, Abbr`c2`, combinTheory.W_DEF] )
      \\ simp[PULL_EXISTS]
      \\ simp[Abbr`d2`, mk_cf_def, restrict_def]
      \\ simp[sum_def, mk_cf_def]
      \\ `c1.env = c2.env` by simp[Abbr`c2`, Abbr`c1`]
      \\ simp[sum_eval_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ `d2.agent = IMAGE (encode_sum o INR) c2.agent` by simp[Abbr`d2`]
      \\ `d2.env = s.env` by simp[Abbr`d2`]
      \\ simp[PULL_EXISTS]
      \\ `s.env = IMAGE (W (CURRY encode_pair)) c2.env`
      by ( simp[Abbr`s`, Abbr`c2`, combinTheory.W_DEF] )
      \\ simp[PULL_EXISTS]
      \\ simp[Abbr`d2`, mk_cf_def, restrict_def]
      \\ simp[sum_def, mk_cf_def]
      \\ `c1.env = c2.env` by simp[Abbr`c2`, Abbr`c1`]
      \\ simp[sum_eval_def] )
    \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
    \\ imp_res_tac maps_to_comp \\ fs[]
    \\ conj_tac \\ irule homotopic_id
    \\ (conj_tac >- metis_tac[maps_to_in_chu])
    \\ (conj_tac >- metis_tac[maps_to_in_chu])
    \\ simp_tac (srw_ss()) [pre_chu_def]
    \\ (conj_tac >- metis_tac[maps_to_in_chu])
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ (conj_tac
    >- (
      simp[composable_in_def]
      \\ simp_tac (srw_ss()) [pre_chu_def]
      \\ metis_tac[maps_to_in_chu] ))
    \\ simp[pre_chu_def, restrict_def]
    \\ simp[Abbr`j`, Abbr`k`, restrict_def]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`d1`, Abbr`d2`]
    \\ simp[FUN_EQ_THM]
    \\ simp[Abbr`s`, PULL_EXISTS]
    \\ disj1_tac
    \\ rw[] \\ rw[] \\ fs[] \\ fs[Abbr`c1`, Abbr`c2`] )
  \\ `s ≃ d' -: c.world` suffices_by metis_tac[homotopy_equiv_trans, homotopy_equiv_sym]
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism s d' <|
       map_agent := λa. sum_CASE (decode_sum a) I I;
       map_env := W (CURRY encode_pair) |>`
  \\ qexists_tac`mk_chu_morphism d' s <|
       map_agent := λa. encode_sum ((if a ∈ x then INL else INR) a);
       map_env := FST o decode_pair |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
  \\ `s ∈ chu_objects c.world`
  by (
    simp[chu_objects_def, Abbr`s`]
    \\ conj_tac
    >- (
      simp[image_def, SUBSET_DEF, PULL_EXISTS]
      \\ simp[sum_def, PULL_EXISTS]
      \\ qpat_x_assum`c1 ∈ _`mp_tac
      \\ qpat_x_assum`c2 ∈ _`mp_tac
      \\ simp[chu_objects_def, wf_def]
      \\ rw[Abbr`c1`, Abbr`c2`, mk_cf_def] \\ rw[] \\ rw[] )
    \\ `finite_cf c1 ∧ finite_cf c2 ∧ finite_cf (sum c1 c2)`
    by (
      full_simp_tac std_ss [chu_objects_def, wf_def]
      \\ rpt(qpat_x_assum`_ ∈ _`mp_tac)
      \\ simp[] )
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[finite_cf_def, Excl"finite_sum"]
    \\ simp[Abbr`c2`] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`k`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, Abbr`s`, mk_cf_def]
    \\ conj_asm1_tac
    >- (
      rw[sum_def] \\ rw[] \\ pop_assum mp_tac
      \\ simp[Abbr`c1`, Abbr`c2`]
      \\ metis_tac[SUBSET_DEF] )
    \\ rw[] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`j`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, Abbr`s`, mk_cf_def, PULL_EXISTS]
    \\ conj_asm1_tac
    >- ( rw[sum_def] \\ simp[Abbr`c1`, Abbr`c2`])
    \\ rw[] )
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ conj_tac \\ irule homotopic_id
  \\ (conj_tac >- metis_tac[maps_to_in_chu])
  \\ (conj_tac >- metis_tac[maps_to_in_chu])
  \\ simp_tac (srw_ss()) [pre_chu_def]
  \\ (conj_tac >- metis_tac[maps_to_in_chu])
  \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ (conj_tac
  >- (
    simp[composable_in_def]
    \\ simp_tac (srw_ss()) [pre_chu_def]
    \\ metis_tac[maps_to_in_chu] ))
  \\ simp[pre_chu_def, restrict_def]
  \\ simp[Abbr`j`, Abbr`k`, restrict_def]
  \\ simp[mk_chu_morphism_def, restrict_def]
  \\ simp[Abbr`s`, Abbr`d'`, PULL_EXISTS]
  \\ simp[FUN_EQ_THM]
  \\ disj1_tac \\ rw[] \\ rw[] \\ fs[]
QED

Theorem is_subtensor_null_null:
  is_subtensor (null w) (null w) n ⇔
    (n = null w ∧ FINITE w) ∨
    (n ≅ cf0 w -: chu w ∧
     n.env = (tensor (null w) (null w)).env)
Proof
  reverse eq_tac
  \\ strip_tac
  >- (
    simp[is_subtensor_def]
    \\ simp[Once tensor_def]
    \\ simp[Once tensor_def]
    \\ simp[restrict_def]
    \\ simp[FUN_EQ_THM]
    \\ qmatch_goalsub_abbrev_tac`_ ≃ nn -: _`
    \\ `nn = null w` suffices_by rw[]
    \\ rw[Abbr`nn`, cf_component_equality, mk_cf_def]
    \\ rw[FUN_EQ_THM] )
  >- (
    `n ∈ chu_objects w`
    by metis_tac[iso_objs_thm, is_category_chu, maps_to_in_chu]
    \\ simp[is_subtensor_def]
    \\ simp[Once tensor_def]
    \\ conj_asm1_tac >- fs[chu_objects_def]
    \\ simp[Once tensor_def]
    \\ conj_asm1_tac >- (
      fs[iso_objs_thm, maps_to_in_chu, is_chu_morphism_def]
      \\ fs[cf0_def] \\ simp[EXTENSION] )
    \\ simp[Once tensor_def, mk_cf_def]
    \\ simp[FUN_EQ_THM]
    \\ conj_tac
    >- ( fs[chu_objects_def, wf_def] \\ simp[restrict_def] )
    \\ qmatch_goalsub_abbrev_tac`_ ≃ nn -: _`
    \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
    \\ `nn = null w` suffices_by rw[]
    \\ rw[Abbr`nn`, cf_component_equality, FUN_EQ_THM] )
  >- (
    fs[is_subtensor_def]
    \\ `null w ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
    \\ Cases_on`n.env = ∅`
    >- (
      disj1_tac
      \\ simp[cf_component_equality]
      \\ simp[tensor_def, FUN_EQ_THM]
      \\ simp[restrict_def] )
    \\ disj2_tac
    \\ reverse conj_asm2_tac
    >- (
      qpat_x_assum`_ ⊆ _`mp_tac
      \\ simp[tensor_def]
      \\ simp[EXTENSION, SUBSET_DEF, hom_def]
      \\ simp[maps_from_null]
      \\ metis_tac[MEMBER_NOT_EMPTY] )
    \\ `n = tensor (null w) (null w)` suffices_by metis_tac[tensor_null_null]
    \\ simp[cf_component_equality]
    \\ simp[FUN_EQ_THM]
    \\ rw[restrict_def]
    \\ `tensor (null w) (null w) ∈ chu_objects w` by simp[]
    \\ pop_assum mp_tac
    \\ simp[chu_objects_def, Excl"tensor_in_chu_objects", Excl"wf_tensor", wf_def])
QED

val _ = export_theory();
