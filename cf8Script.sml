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
  pairTheory pred_setTheory helperSetTheory categoryTheory
  cf0Theory cf1Theory cf2Theory cf4Theory cf5Theory cf6Theory cf7Theory

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

Theorem sister_in_chu_objects:
  is_sister d c c' ⇒
    d ∈ chu_objects c.world ∧
    c ∈ chu_objects c.world ∧
    c' ∈ chu_objects c.world
Proof
  simp[is_sister_def]
  \\ strip_tac
  \\ conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
  \\ full_simp_tac std_ss [is_subtensor_def]
  \\ metis_tac[homotopy_equiv_def, maps_to_in_chu]
QED

Theorem is_sister_homotopy_equiv:
  is_sister d c c' ∧
  d1 ≃ d -: w ∧ c1 ≃ c -: w ∧ c1' ≃ c' -: w ⇒
  is_sister d1 c1 c1'
Proof
  strip_tac
  \\ imp_res_tac sister_in_chu_objects
  \\ fs[is_sister_def]
  \\ `c.world = w` by (
    `c ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [chu_objects_def]
    \\ simp[] )
  \\ first_assum(mp_then(Pat`is_subtensor`)mp_tac subtensor_homotopy_equiv)
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

Theorem multiplicative_subagent_externalising:
  multiplicative_subagent c d ⇔
  ∃x y z f.
    c ≃ mk_cf <| world := c.world;
                 agent := x;
                 env := IMAGE encode_pair (y × z);
                 eval := λa e. UNCURRY (f a) (decode_pair e) |>
        -: c.world ∧
    d ≃ mk_cf <| world := c.world;
                 agent := IMAGE encode_pair (x × y);
                 env := z;
                 eval := UNCURRY f o decode_pair |>
        -: c.world ∧
    FINITE y
Proof
  eq_tac
  >- (
    rw[multiplicative_subagent_sister]
    \\ fs[is_sister_def]
    \\ qexists_tac`c.agent`
    \\ qexists_tac`c'.agent`
    \\ qexists_tac`d'.env`
    \\ qexists_tac`λx y z. c.eval x ((decode_morphism c (swap c') z).map.map_env y)`
    \\ simp[]
    \\ qmatch_goalsub_abbrev_tac`c ≃ c1 -: _`
    \\ qmatch_goalsub_abbrev_tac`d ≃ d1 -: _`
    \\ `d1.agent = (tensor c c').agent` by (
      simp[Abbr`d1`, tensor_def])
    \\ `c' ∈ chu_objects c'.world` by metis_tac[is_subtensor_def, homotopy_equiv_def, maps_to_in_chu]
    \\ `finite_cf c'` by fs[chu_objects_def, wf_def]
    \\ fs[finite_cf_def]
    \\ reverse conj_tac
    >- (
      `d1 = d'` suffices_by rw[]
      \\ fs[Abbr`d1`, Abbr`c1`]
      \\ fs[is_subtensor_def]
      \\ simp[cf_component_equality]
      \\ simp[Once tensor_def]
      \\ simp[mk_cf_def, FUN_EQ_THM, EXISTS_PROD, PULL_EXISTS]
      \\ simp[restrict_def]
      \\ rpt gen_tac
      \\ reverse IF_CASES_TAC \\ simp[]
      >- (
        fs[]
        \\ IF_CASES_TAC \\ simp[]
        \\ simp[Once tensor_def, mk_cf_def] )
      \\ fs[SUBSET_DEF]
      \\ first_x_assum drule
      \\ simp[Once tensor_def, hom_def]
      \\ strip_tac
      \\ qpat_x_assum`x ∈ _`mp_tac
      \\ simp_tac(srw_ss())[Once tensor_def, EXISTS_PROD]
      \\ strip_tac
      \\ simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
      \\ conj_tac >- metis_tac[]
      \\ simp[Once tensor_def, mk_cf_def, hom_def]
      \\ simp_tac(srw_ss())[Once tensor_def]
      \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
      \\ conj_asm1_tac >- metis_tac[]
      \\ simp[] \\ metis_tac[] )
    \\ fs[is_subtensor_def]
    \\ qmatch_assum_abbrev_tac`c ≃ c2 -: _`
    \\ `c1 = c2` suffices_by rw[]
    \\ simp[Abbr`c1`, Abbr`c2`, cf_component_equality]
    \\ simp[mk_cf_def, FUN_EQ_THM, EXISTS_PROD]
    \\ rpt gen_tac
    \\ IF_CASES_TAC \\ simp[]
    \\ simp[restrict_def]
    \\ fs[]
    \\ simp[Once tensor_def, mk_cf_def]
    \\ rw[]
    \\ fs[SUBSET_DEF]
    \\ first_x_assum drule
    \\ simp[tensor_def]
    \\ metis_tac[] )
  \\ strip_tac
  \\ Cases_on`x = ∅ ∧ y = ∅`
  >- (
    fs[]
    \\ qmatch_assum_abbrev_tac`c ≃ n -: _`
    \\ `n = null c.world`
    by (
      simp[cf_component_equality, Abbr`n`]
      \\ simp[null_def, mk_cf_def, FUN_EQ_THM] )
    \\ qmatch_assum_abbrev_tac`d ≃ d' -: _`
    \\ simp[multiplicative_subagent_def]
    \\ qexists_tac`c` \\ simp[]
    \\ `n ∈ chu_objects c.world` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ `FINITE c.world` by metis_tac[in_chu_objects_finite_world]
    \\ `∃d'. d' ≃ d -: c.world ∧
             is_subtensor n n d'` suffices_by (
      strip_tac
      \\ `∃d3. d3 ≃ d'' -: c.world ∧ is_subtensor c c d3`
      by metis_tac[subtensor_homotopy_equiv]
      \\ qexists_tac`d3` \\ simp[]
      \\ metis_tac[homotopy_equiv_sym, homotopy_equiv_trans] )
    \\ simp[is_subtensor_null_null]
    \\ Cases_on`z = ∅`
    >- (
      qexists_tac`d'`
      \\ simp[homotopy_equiv_sym]
      \\ disj1_tac
      \\ simp[cf_component_equality]
      \\ simp[Abbr`d'`, mk_cf_def, FUN_EQ_THM])
    \\ qmatch_goalsub_abbrev_tac`_.env = ev`
    \\ qexists_tac`d' with env := ev` \\ simp[]
    \\ dsimp[]
    \\ disj2_tac
    \\ qmatch_goalsub_abbrev_tac`d1 ≃ d -: w`
    \\ `d' ∈ chu_objects w` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ `d1 ∈ chu_objects w` by (
      pop_assum mp_tac
      \\ simp_tac(std_ss)[Abbr`d1`]
      \\ rewrite_tac[chu_objects_def]
      \\ simp[wf_def]
      \\ simp[Abbr`d'`, mk_cf_def, finite_cf_def]
      \\ rw[Abbr`ev`, tensor_def]
      \\ irule IMAGE_FINITE
      \\ simp[hom_def, maps_from_null] )
    \\ conj_asm1_tac
    >- (
      irule homotopy_equiv_trans
      \\ qexists_tac`d'`
      \\ simp[homotopy_equiv_sym]
      \\ simp[homotopy_equiv_def]
      \\ qexists_tac`mk_chu_morphism d' d1 <| map_agent := I; map_env := K (CHOICE z) |>`
      \\ qexists_tac`mk_chu_morphism d1 d' <| map_agent := I; map_env := K (CHOICE ev) |>`
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu]
        \\ simp[mk_chu_morphism_def, is_chu_morphism_def]
        \\ simp[restrict_def]
        \\ simp[Abbr`d'`]
        \\ metis_tac[CHOICE_DEF] )
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu]
        \\ simp[mk_chu_morphism_def, is_chu_morphism_def]
        \\ simp[restrict_def]
        \\ simp[Abbr`d'`, Abbr`d1`]
        \\ rw[]
        \\ irule CHOICE_DEF
        \\ simp[Abbr`ev`, tensor_def, hom_def, maps_from_null] )
      \\ imp_res_tac maps_to_comp \\ fs[]
      \\ fs[maps_to_in_chu]
      \\ conj_tac \\ irule homotopic_id \\ simp[pre_chu_def]
      \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
      \\ simp[composable_in_def]
      \\ simp[pre_chu_def]
      \\ simp[restrict_def, mk_chu_morphism_def]
      \\ simp[Abbr`d1`] )
    \\ simp[iso_objs_thm]
    \\ qexists_tac`mk_chu_morphism d1 (cf0 w) <| map_agent := I; map_env := K (CHOICE ev) |>`
    \\ simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, chu_iso_bij, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d1`]
    \\ simp[cf0_def]
    \\ simp[Abbr`d'`]
    \\ `ev = {CHOICE ev}`
    by (
      simp[EXTENSION, Abbr`ev`, tensor_def, hom_def, maps_from_null] )
    \\ qmatch_assum_abbrev_tac`ev = {e}`
    \\ simp[BIJ_IFF_INV]
    \\ qexists_tac`K ""` \\ simp[] )
  \\ simp[multiplicative_subagent_sister]
  \\ qmatch_assum_abbrev_tac`c ≃ c1 -: _`
  \\ `∃c'. is_sister d c1 c'` suffices_by (
    strip_tac
    \\ drule is_sister_homotopy_equiv
    \\ disch_then(qspecl_then[`c.world`,`d`]mp_tac)
    \\ `d ∈ chu_objects c.world` by metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ simp[]
    \\ disch_then drule
    \\ imp_res_tac sister_in_chu_objects
    \\ `c1.world = c.world` by simp[Abbr`c1`]
    \\ metis_tac[homotopy_equiv_refl] )
  \\ qexists_tac`mk_cf <| world := c.world;
       agent := y; env := IMAGE encode_pair (x × z);
       eval := λy xz. f (FST (decode_pair xz)) y (SND (decode_pair xz)) |>`
  \\ qmatch_goalsub_abbrev_tac`is_sister d c1 c2`
  \\ simp[is_sister_def]
  \\ `c1.world = c.world ∧ c2.world = c.world` by simp[Abbr`c1`, Abbr`c2`]
  \\ qmatch_assum_abbrev_tac`¬ empty_x_y`
  \\ gs[]
  \\ qmatch_assum_abbrev_tac`d ≃ d' -: _`
  \\ `c1 ∈ chu_objects c.world ∧ d' ∈ chu_objects c.world ∧
      c2 ∈ chu_objects c.world`
  by (
    conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ conj_asm1_tac >- metis_tac[homotopy_equiv_def, maps_to_in_chu]
    \\ qpat_x_assum`c1 ∈ _`mp_tac
    \\ qpat_x_assum`d' ∈ _`mp_tac
    \\ simp[Abbr`d'`, Abbr`c1`, Abbr`c2`, in_chu_objects]
    \\ simp[SUBSET_DEF, image_def, finite_cf_def, PULL_EXISTS, EXISTS_PROD])
  \\ `∀zz. zz ∈ z ⇒ (mk_chu_morphism c1 (swap c2) <| map_agent := λx. encode_pair (x, zz); map_env := λy. encode_pair (y, zz) |>) :- c1 → (swap c2) -: chu c.world`
  by (
    simp[is_chu_morphism_def, mk_chu_morphism_def, maps_to_in_chu]
    \\ simp[restrict_def]
    \\ simp[Abbr`c1`, Abbr`c2`, mk_cf_def] )
  \\ pop_assum mp_tac
  \\ qho_match_abbrev_tac`(∀zz. _ zz ⇒ (g zz) :- _ → _ -: _) ⇒ _`
  \\ simp[] \\ strip_tac
  \\ qexists_tac`mk_cf <| world := c.world;
       agent := (tensor c1 c2).agent;
       env := IMAGE (encode_morphism o g) z;
       eval := (tensor c1 c2).eval |>`
  \\ qmatch_goalsub_abbrev_tac`is_subtensor c1 c2 s`
  \\ `INJ g z (IMAGE g z)`
  by (
    simp[INJ_DEF]
    \\ simp[Abbr`g`]
    \\ simp[morphism_component_equality, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c1`, Abbr`c2`]
    \\ simp[FUN_EQ_THM]
    \\ rw[]
    \\ qpat_x_assum`_ = F`mp_tac
    \\ simp[GSYM MEMBER_NOT_EMPTY]
    \\ strip_tac
    \\ qmatch_assum_rename_tac`j ∈ _`
    \\ ntac 2 (first_x_assum(qspec_then`j`mp_tac))
    \\ simp[])
  \\ `BIJ g z (IMAGE g z)` by simp[BIJ_DEF]
  \\ `BIJ (encode_morphism o g) z s.env`
  by (
    irule BIJ_COMPOSE
    \\ qexists_tac`IMAGE g z`
    \\ simp[]
    \\ simp[BIJ_IFF_INV, PULL_EXISTS]
    \\ qexists_tac`decode_morphism c1 (swap c2)`
    \\ simp[Abbr`s`, PULL_EXISTS]
    \\ metis_tac[decode_encode_chu_morphism] )
  \\ reverse conj_tac
  >- (
    simp[is_subtensor_def]
    \\ conj_asm1_tac >- simp[tensor_def, Abbr`s`]
    \\ conj_asm1_tac >- simp[Abbr`s`]
    \\ conj_asm1_tac
    >- (
      simp[Abbr`s`, tensor_def, SUBSET_DEF, PULL_EXISTS, hom_def]
      \\ metis_tac[])
    \\ conj_asm1_tac
    >- (
      simp[Abbr`s`,mk_cf_def,restrict_def,PULL_EXISTS]
      \\ gen_tac
      \\ simp[FUN_EQ_THM]
      \\ Cases_on`a ∈ (tensor c1 c2).agent` \\ simp[]
      \\ pop_assum mp_tac
      \\ rw[tensor_def, mk_cf_def]
      \\ metis_tac[])
    \\ qmatch_goalsub_abbrev_tac`c1 ≃ d1 -: _`
    \\ qmatch_goalsub_abbrev_tac`c2 ≃ d2 -: _`
    \\ `d1 ∈ chu_objects c.world ∧ d2 ∈ chu_objects c.world`
    by (
      `finite_cf d1 ∧ finite_cf d2`
      by (
        `finite_cf c1 ∧ finite_cf c2`
        by (
          ntac 3 (qpat_x_assum`_ ∈ _`mp_tac)
          \\ simp_tac(srw_ss())[in_chu_objects]
          \\ simp[wf_def] )
        \\ `finite_cf (tensor c1 c2)` by metis_tac[finite_tensor]
        \\ ntac 3 (pop_assum mp_tac)
        \\ simp[Abbr`d1`, Abbr`d2`, finite_cf_def, Excl"finite_tensor"]
        \\ metis_tac[SUBSET_FINITE] )
      \\ `wf c1 ∧ wf c2` by fs[in_chu_objects]
      \\ qpat_x_assum`finite_cf _`mp_tac
      \\ qpat_x_assum`finite_cf _`mp_tac
      \\ simp[chu_objects_def, Abbr`d1`, Abbr`d2`, finite_cf_def]
      \\ simp[SUBSET_DEF, image_def, PULL_EXISTS, EXISTS_PROD]
      \\ simp[restrict_def]
      \\ simp[tensor_def, mk_cf_def, PULL_EXISTS, hom_def]
      \\ disch_then kall_tac
      \\ disch_then kall_tac
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp_tac(srw_ss())[wf_def]
      \\ rw[] \\ rw[]
      \\ TRY(qpat_x_assum`_ ∈ s.env`mp_tac \\ simp_tac(srw_ss())[Abbr`s`] \\ strip_tac)
      \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def, swap_components] )
    \\ conj_tac
    >- (
      simp[homotopy_equiv_def]
      \\ qexists_tac`mk_chu_morphism c1 d1
           <| map_agent := I;
              map_env := encode_pair o pair$## I (LINV (encode_morphism o g) z)
                           o decode_pair |>`
      \\ qexists_tac`mk_chu_morphism d1 c1
           <| map_agent := I;
              map_env :=  encode_pair o pair$## I (encode_morphism o g) o decode_pair |>`
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu]
        \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
        \\ simp[restrict_def]
        \\ `d1.agent = c1.agent` by simp[Abbr`d1`]
        \\ `d1.env = IMAGE encode_pair (y × s.env)` by simp[Abbr`d1`, Abbr`c2`]
        \\ `c1.env = IMAGE encode_pair (y × z)` by simp[Abbr`c1`]
        \\ `s.env = IMAGE (encode_morphism o g) z` by simp[Abbr`s`]
        \\ simp[PULL_EXISTS, EXISTS_PROD, Excl"o_THM"]
        \\ conj_tac >- metis_tac[BIJ_LINV_THM]
        \\ drule BIJ_LINV_THM \\ simp[] \\ disch_then kall_tac
        \\ `c1.agent = x` by simp[Abbr`c1`] \\ simp[]
        \\ qx_genl_tac[`j`,`k`,`l`] \\ strip_tac
        \\ `c1.eval j (encode_pair (k,l)) = f j k l`
        by simp[Abbr`c1`, mk_cf_def]
        \\ `c2.agent = y` by simp[Abbr`c2`]
        \\ simp[Abbr`d1`, mk_cf_def, restrict_def]
        \\ simp[Once tensor_def, mk_cf_def, hom_def]
        \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
        \\ conj_tac >- metis_tac[]
        \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
        \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
        \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def])
      \\ conj_asm1_tac
      >- (
        simp[maps_to_in_chu]
        \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
        \\ simp[restrict_def]
        \\ `d1.agent = c1.agent` by simp[Abbr`d1`]
        \\ `d1.env = IMAGE encode_pair (y × s.env)` by simp[Abbr`d1`, Abbr`c2`]
        \\ `c1.env = IMAGE encode_pair (y × z)` by simp[Abbr`c1`]
        \\ `s.env = IMAGE (encode_morphism o g) z` by simp[Abbr`s`]
        \\ simp[PULL_EXISTS, EXISTS_PROD]
        \\ conj_tac >- metis_tac[]
        \\ `c1.agent = x` by simp[Abbr`c1`] \\ simp[]
        \\ qx_genl_tac[`j`,`k`,`l`] \\ strip_tac
        \\ `c1.eval j (encode_pair (k,l)) = f j k l`
        by simp[Abbr`c1`, mk_cf_def]
        \\ `c2.agent = y` by simp[Abbr`c2`]
        \\ simp[Abbr`d1`, mk_cf_def, restrict_def]
        \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
        \\ simp[Once tensor_def, mk_cf_def, hom_def]
        \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
        \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
        \\ conj_tac >- metis_tac[]
        \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def])
      \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
      \\ simp[homotopic_id_map_agent_id]
      \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
      \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
      \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
      \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
      \\ simp[Abbr`j`, Abbr`k`, restrict_def]
      \\ simp[mk_chu_morphism_def, restrict_def]
      \\ simp[Abbr`d1`])
    \\ simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c2 d2
         <| map_agent := I;
            map_env := encode_pair o pair$## I (LINV (encode_morphism o g) z)
                         o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism d2 c2
         <| map_agent := I;
            map_env :=  encode_pair o pair$## I (encode_morphism o g) o decode_pair |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ `d2.agent = c2.agent` by simp[Abbr`d2`]
      \\ `d2.env = IMAGE encode_pair (x × s.env)` by simp[Abbr`d2`, Abbr`c1`]
      \\ `c2.env = IMAGE encode_pair (x × z)` by simp[Abbr`c2`]
      \\ `s.env = IMAGE (encode_morphism o g) z` by simp[Abbr`s`]
      \\ simp[PULL_EXISTS, EXISTS_PROD, Excl"o_THM"]
      \\ conj_tac >- metis_tac[BIJ_LINV_THM]
      \\ drule BIJ_LINV_THM \\ simp[] \\ disch_then kall_tac
      \\ `c2.agent = y` by simp[Abbr`c2`] \\ simp[]
      \\ qx_genl_tac[`j`,`k`,`l`] \\ strip_tac
      \\ `c2.eval j (encode_pair (k,l)) = f k j l`
      by simp[Abbr`c2`, mk_cf_def]
      \\ `c1.agent = x` by simp[Abbr`c1`]
      \\ simp[Abbr`d2`, mk_cf_def, restrict_def]
      \\ simp[Once tensor_def, mk_cf_def, hom_def]
      \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
      \\ conj_tac >- metis_tac[]
      \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
      \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
      \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def]
      \\ simp[Abbr`c1`, mk_cf_def])
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ `d2.agent = c2.agent` by simp[Abbr`d2`]
      \\ `d2.env = IMAGE encode_pair (x × s.env)` by simp[Abbr`d2`, Abbr`c1`]
      \\ `c2.env = IMAGE encode_pair (x × z)` by simp[Abbr`c2`]
      \\ `s.env = IMAGE (encode_morphism o g) z` by simp[Abbr`s`]
      \\ simp[PULL_EXISTS, EXISTS_PROD]
      \\ conj_tac >- metis_tac[]
      \\ `c2.agent = y` by simp[Abbr`c2`] \\ simp[]
      \\ qx_genl_tac[`j`,`k`,`l`] \\ strip_tac
      \\ `c2.eval j (encode_pair (k,l)) = f k j l`
      by simp[Abbr`c2`, mk_cf_def]
      \\ `c1.agent = x` by simp[Abbr`c1`]
      \\ simp[Abbr`d2`, mk_cf_def, restrict_def]
      \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
      \\ simp[Once tensor_def, mk_cf_def, hom_def]
      \\ reverse IF_CASES_TAC >- metis_tac[] \\ pop_assum kall_tac
      \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
      \\ conj_tac >- metis_tac[]
      \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def]
      \\ simp[Abbr`c1`, mk_cf_def])
    \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
    \\ simp[homotopic_id_map_agent_id]
    \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
    \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
    \\ simp[Abbr`j`, Abbr`k`, restrict_def]
    \\ simp[mk_chu_morphism_def, restrict_def]
    \\ simp[Abbr`d2`])
  \\ `s ≃ d' -: c.world` suffices_by metis_tac[homotopy_equiv_trans, homotopy_equiv_sym]
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism s d' <|
       map_agent := I;
       map_env := encode_morphism o g |>`
  \\ qexists_tac`mk_chu_morphism d' s <|
       map_agent := I;
       map_env := LINV (encode_morphism o g) z |>`
  \\ qmatch_goalsub_abbrev_tac`homotopic _ (j o k -: _)`
  \\ `s ∈ chu_objects c.world`
  by (
    simp[in_chu_objects, Abbr`s`]
    \\ conj_tac
    >- (
      simp[image_def, SUBSET_DEF, PULL_EXISTS]
      \\ `tensor c1 c2 ∈ chu_objects c.world` by simp[]
      \\ pop_assum mp_tac
      \\ simp_tac (srw_ss()) [in_chu_objects, wf_def, Excl"tensor_in_chu_objects", Excl"wf_tensor"]
      \\ strip_tac \\ fs[] \\ rpt strip_tac
      \\ first_x_assum irule \\ simp[]
      \\ simp[tensor_def, hom_def])
    \\ `finite_cf c1 ∧ finite_cf c2 ∧ finite_cf d' ∧ finite_cf (tensor c1 c2)`
    by (
      full_simp_tac std_ss [in_chu_objects, wf_def]
      \\ rpt(qpat_x_assum`_ ∈ _`mp_tac)
      \\ simp[] )
    \\ ntac 4 (pop_assum mp_tac)
    \\ simp[finite_cf_def, Excl"finite_tensor"]
    \\ simp[Abbr`c2`, Abbr`c1`, Abbr`d'`] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`k`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, Abbr`s`, mk_cf_def, EXISTS_PROD, PULL_EXISTS]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[Once tensor_def, mk_cf_def, hom_def]
    \\ conj_tac >- metis_tac[]
    \\ conj_asm1_tac
    >- simp[Abbr`c1`, Abbr`c2`]
    \\ rpt strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
    \\ conj_tac >- metis_tac[]
    \\ res_tac
    \\ simp[Abbr`c1`, mk_cf_def, EXISTS_PROD]
    \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def])
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu, Abbr`j`]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d'`, Abbr`s`, mk_cf_def, EXISTS_PROD, PULL_EXISTS, Excl"o_THM"]
    \\ conj_tac >- metis_tac[BIJ_LINV_THM]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ conj_asm1_tac >- simp[Abbr`c1`, Abbr`c2`]
    \\ rpt strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[BIJ_LINV_THM, combinTheory.o_THM]
    \\ simp[Once tensor_def, PULL_EXISTS, EXISTS_PROD]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ simp[Once tensor_def, mk_cf_def, hom_def]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[Q.GEN`w`decode_encode_chu_morphism]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`c1`, mk_cf_def, EXISTS_PROD]
    \\ qmatch_goalsub_abbrev_tac`f _ _ xx`
    \\ `xx = x'` by metis_tac[BIJ_LINV_THM, combinTheory.o_THM]
    \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def])
  \\ simp[homotopic_id_map_agent_id]
  \\ qpat_assum`j :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`k :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ qpat_assum`k :- _ → _ -: _`(mp_then Any mp_tac compose_in_chu)
  \\ disch_then(qpat_assum`j :- _ → _ -: _` o mp_then Any strip_assume_tac)
  \\ simp[Abbr`j`, Abbr`k`, restrict_def]
  \\ simp[mk_chu_morphism_def, restrict_def]
  \\ simp[Abbr`s`, Abbr`d'`, PULL_EXISTS, EXISTS_PROD]
  \\ simp[FUN_EQ_THM]
  \\ simp[tensor_def, EXISTS_PROD, PULL_EXISTS, Abbr`c1`, Abbr`c2`]
QED

Theorem additive_subagent_currying:
  additive_subagent c d ⇔
  ∃m. m ∈ chu_objects d.agent ∧ SING m.env ∧ c ≃ move d m -: c.world ∧
      d ∈ chu_objects c.world
Proof
  simp[additive_subagent_committing]
  \\ eq_tac \\ strip_tac
  >- (
    qmatch_assum_abbrev_tac`d ≃ d' -: w`
    \\ qmatch_assum_abbrev_tac`c ≃ c' -: w`
    \\ qho_match_abbrev_tac`P c`
    \\ `P c'` suffices_by (
      simp[Abbr`P`]
      \\ metis_tac[homotopy_equiv_sym, homotopy_equiv_trans] )
    \\ fs[homotopy_equiv_def, Abbr`P`]
    \\ qmatch_assum_rename_tac`j :- d → d' -: _`
    \\ qmatch_assum_rename_tac`k :- d' → d -: _`
    \\ qexists_tac`mk_cf <| world := d.agent; agent := x; env := {""};
                            eval := λa e. k.map.map_agent a |>`
    \\ `d ∈ chu_objects w ∧ c ∈ chu_objects w ∧ c' ∈ chu_objects w`
    by metis_tac[maps_to_in_chu]
    \\ conj_asm1_tac
    >- (
      ntac 3 (pop_assum mp_tac)
      \\ simp[chu_objects_def]
      \\ simp[wf_def]
      \\ simp[finite_cf_def]
      \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
      \\ `d'.agent = y` by simp[Abbr`d'`]
      \\ simp[Abbr`c'`]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def, SUBSET_DEF] )
    \\ conj_tac >- simp[mk_cf_def]
    \\ qmatch_goalsub_abbrev_tac`move d m`
    \\ simp[]
    \\ qexists_tac`mk_chu_morphism c' (move d m) <| map_agent := I;
         map_env := k.map.map_env o SND o decode_pair |>`
    \\ qexists_tac`mk_chu_morphism (move d m) c' <| map_agent := I;
         map_env := λe. encode_pair ("", j.map.map_env e) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def,
              PULL_EXISTS, EXISTS_PROD]
      \\ simp[restrict_def]
      \\ `d'.env = z ∧ c'.env = z` by simp[Abbr`d'`, Abbr`c'`]
      \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ `c'.agent = x ∧ m.agent = x` by simp[Abbr`c'`, Abbr`m`]
      \\ conj_tac >- metis_tac[]
      \\ simp[move_def]
      \\ `∀a. a ∈ x ⇒ c'.eval a = d'.eval a`
      by (
        simp[Abbr`c'`, Abbr`d'`, mk_cf_def, FUN_EQ_THM]
        \\ metis_tac[SUBSET_DEF] )
      \\ simp[Abbr`m`, mk_cf_def]
      \\ `d'.agent = y` by simp[Abbr`d'`]
      \\ metis_tac[SUBSET_DEF, maps_to_in_chu, is_chu_morphism_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def,
              PULL_EXISTS, EXISTS_PROD]
      \\ simp[restrict_def]
      \\ `d'.env = z ∧ c'.env = z` by simp[Abbr`d'`, Abbr`c'`]
      \\ `m.env = {""}` by simp[Abbr`m`]
      \\ `c'.agent = x ∧ m.agent = x` by simp[Abbr`c'`, Abbr`m`]
      \\ simp[]
      \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[move_def, mk_cf_def]
      \\ `∀a. a ∈ x ⇒ c'.eval a = d'.eval a`
      by (
        simp[Abbr`c'`, Abbr`d'`, mk_cf_def, FUN_EQ_THM]
        \\ metis_tac[SUBSET_DEF] )
      \\ simp[Abbr`m`, mk_cf_def]
      \\ `d'.agent = y` by simp[Abbr`d'`]
      \\ rpt strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ qpat_x_assum`homotopic _ (j o k -: _) _`mp_tac
      \\ DEP_REWRITE_TAC[homotopic_id_map_env_id]
      \\ conj_tac >- metis_tac[maps_to_in_chu]
      \\ strip_tac \\ gs[]
      \\ first_x_assum drule
      \\ disch_then (fn th => simp[Once(GSYM th)])
      \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
      \\ conj_tac
      >- ( simp[composable_in_def, pre_chu_def] \\ metis_tac[maps_to_in_chu] )
      \\ `j.cod = d'` by metis_tac[maps_to_in_chu]
      \\ simp[pre_chu_def, restrict_def]
      \\ metis_tac[SUBSET_DEF, maps_to_in_chu, is_chu_morphism_def] )
    \\ qmatch_goalsub_abbrev_tac`p o q -: _`
    \\ imp_res_tac maps_to_comp \\ fs[]
    \\ qpat_x_assum`p o q -: _ :- _ → _ -: _`mp_tac
    \\ qpat_x_assum`q o p -: _ :- _ → _ -: _`mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ conj_tac
    >- (
      fs[Abbr`p`, Abbr`q`, mk_chu_morphism_def, composable_in_def]
      \\ simp[pre_chu_def] \\ fs[maps_to_in_chu] )
    \\ simp[pre_chu_def, mk_chu_morphism_def, Abbr`p`, Abbr`q`]
    \\ `c'.agent = x ∧ m.agent = x` by simp[Abbr`c'`, Abbr`m`]
    \\ ntac 2 strip_tac
    \\ conj_tac \\ irule homotopic_id \\ gs[restrict_def]
    \\ simp[pre_chu_def] \\ fs[maps_to_in_chu] )
  \\ qexists_tac`image m`
  \\ qexists_tac`d.agent`
  \\ qexists_tac`d.env`
  \\ qexists_tac`d.eval`
  \\ conj_asm1_tac
  >- (
    simp[image_def]
    \\ gs[chu_objects_def, wf_def, SUBSET_DEF, PULL_EXISTS] )
  \\ reverse conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`d ≃ d' -: _`
    \\ `d' = d`
    by (
      simp[Abbr`d'`, cf_component_equality, mk_cf_def]
      \\ fs[chu_objects_def, wf_def]
      \\ simp[FUN_EQ_THM]
      \\ rw[] \\ metis_tac[] )
    \\ rw[] )
  \\ `m ≃ cfbot d.agent (image m) -: d.agent` by imp_res_tac sing_env
  \\ `c ≃ move d (cfbot d.agent (image m)) -: c.world`
  by (
    irule homotopy_equiv_trans
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule homotopy_equiv_move
    \\ metis_tac[] )
  \\ irule homotopy_equiv_trans
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qmatch_goalsub_abbrev_tac`d1 ≃ d2 -: w`
  \\ `d1 ∈ chu_objects w`
  by (
    simp[Abbr`d1`]
    \\ irule move_in_chu_objects
    \\ simp[]
    \\ irule cfbot_in_chu_objects
    \\ metis_tac[in_chu_objects_finite_world] )
  \\ `d2 ∈ chu_objects w`
  by (
    simp[Abbr`d2`]
    \\ qpat_x_assum`d ∈ _`mp_tac
    \\ qpat_x_assum`m ∈ _`mp_tac
    \\ simp[chu_objects_def]
    \\ simp[wf_def, finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ rw[]
    \\ metis_tac[] )
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism d1 d2 <| map_agent := I; map_env := λe. encode_pair ("", e) |>`
  \\ qexists_tac`mk_chu_morphism d2 d1 <| map_agent := I; map_env := SND o decode_pair |>`
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d2`, Abbr`d1`, mk_cf_def]
    \\ simp[move_def, cfbot_def]
    \\ simp[cf1_def, mk_cf_def] )
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`d2`, Abbr`d1`, mk_cf_def, PULL_EXISTS, EXISTS_PROD]
    \\ simp[move_def, cfbot_def]
    \\ simp[cf1_def, mk_cf_def] )
  \\ rw[homotopic_id_map_agent_id]
  \\ TRY(irule maps_to_comp \\ simp[] \\ metis_tac[])
  \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ (conj_tac >- (fs[composable_in_def, maps_to_in_chu, pre_chu_def]))
  \\ simp[pre_chu_def, restrict_def, mk_chu_morphism_def]
  \\ rw[]
  \\ fs[Abbr`d1`, Abbr`d2`, cfbot_def]
QED

Theorem multiplicative_subagent_currying:
  multiplicative_subagent c d ⇔
  ∃m. m ∈ chu_objects d.agent ∧ image m = d.agent ∧ c ≃ move d m -: c.world ∧
      d ∈ chu_objects c.world
Proof
  simp[multiplicative_subagent_externalising]
  \\ eq_tac \\ strip_tac
  >- (
    qmatch_assum_abbrev_tac`c ≃ c' -: w`
    \\ qmatch_assum_abbrev_tac`d ≃ d' -: w`
    \\ qho_match_abbrev_tac`P c`
    \\ `P c'` suffices_by (
      simp[Abbr`P`] \\ metis_tac[homotopy_equiv_trans] )
    \\ simp[Abbr`P`]
    \\ fs[homotopy_equiv_def]
    \\ qmatch_assum_rename_tac`j :- d → d' -: _`
    \\ qmatch_assum_rename_tac`k :- d' → d -: _`
    \\ qabbrev_tac`b' = IMAGE encode_sum (IMAGE INL d.agent ∪ {INR ""})`
    \\ qexists_tac`mk_cf <| world := d.agent; agent := x;
         env := IMAGE encode_pair (y × b');
         eval := λa e. if ISL (decode_sum (SND (decode_pair e))) ∧
                          j.map.map_agent (OUTL (decode_sum (SND (decode_pair e)))) = encode_pair (a, FST (decode_pair e))
                       then OUTL (decode_sum (SND (decode_pair e)))
                       else k.map.map_agent (encode_pair (a, FST (decode_pair e))) |>`
    \\ qmatch_goalsub_abbrev_tac`image m`
    \\ `d ∈ chu_objects w ∧ c ∈ chu_objects w ∧ c' ∈ chu_objects w`
    by metis_tac[maps_to_in_chu]
    \\ conj_asm1_tac
    >- (
      ntac 3 (pop_assum mp_tac)
      \\ simp[chu_objects_def, Abbr`m`]
      \\ simp[wf_def, finite_cf_def]
      \\ simp[Abbr`c'`]
      \\ simp[image_def, SUBSET_DEF, PULL_EXISTS, Abbr`b'`, EXISTS_PROD, mk_cf_def]
      \\ rw[] \\ rw[] \\ fs[]
      \\ fs[maps_to_in_chu, is_chu_morphism_def]
      \\ first_x_assum irule \\ simp[Abbr`d'`] )
    \\ conj_asm1_tac
    >- (
      rw[SET_EQ_SUBSET]
      >- (
        pop_assum mp_tac
        \\ simp[chu_objects_def, wf_def, image_def, SUBSET_DEF, PULL_EXISTS]
        \\ metis_tac[] )
      \\ simp[image_def, Abbr`m`, mk_cf_def,
              PULL_EXISTS, EXISTS_PROD, SUBSET_DEF]
      \\ qx_gen_tac`a` \\ strip_tac
      \\ qexists_tac`FST (decode_pair (j.map.map_agent a))`
      \\ qexists_tac`SND (decode_pair (j.map.map_agent a))`
      \\ qexists_tac`encode_sum (INL a)`
      \\ `j.map.map_agent a ∈ d'.agent` by metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ pop_assum mp_tac
      \\ simp[Abbr`d'`, EXISTS_PROD]
      \\ strip_tac
      \\ simp[Abbr`b'`] )
    \\ simp[]
    \\ qexists_tac`mk_chu_morphism c' (move d m) <| map_agent := I;
         map_env := λe. encode_pair (FST (decode_pair (FST (decode_pair e))),
                                     k.map.map_env (SND (decode_pair e))) |>`
    \\ qexists_tac`mk_chu_morphism (move d m) c' <| map_agent := I;
         map_env := λe. encode_pair (encode_pair (FST (decode_pair e),
                                                  encode_sum(INR "")),
                                     j.map.map_env (SND (decode_pair e))) |>`
    \\ qmatch_goalsub_abbrev_tac`p o q -: _`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`q`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def,
              PULL_EXISTS, EXISTS_PROD]
      \\ simp[restrict_def]
      \\ `c'.agent = x ∧ m.agent = x ∧ m.env = IMAGE encode_pair (y × b') ∧
          c'.env = IMAGE encode_pair (y × z)` by simp[Abbr`c'`, Abbr`m`]
      \\ simp[PULL_EXISTS, EXISTS_PROD]
      \\ `d'.env = z` by simp[Abbr`d'`]
      \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[Abbr`c'`, mk_cf_def]
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ qmatch_goalsub_abbrev_tac`d.eval aa`
      \\ qmatch_assum_rename_tac`b ∈ y`
      \\ `d.eval aa = d.eval (k.map.map_agent (encode_pair (a,b)))`
      by (
        qpat_x_assum`_ ∈ b'`mp_tac
        \\ simp[Abbr`b'`, PULL_EXISTS]
        \\ reverse(rw[Abbr`aa`])
        >- ( fs[Abbr`m`, mk_cf_def] )
        \\ qpat_x_assum`a ∈ _`mp_tac
        \\ simp[Abbr`m`, mk_cf_def]
        \\ rw[]
        \\ qpat_x_assum`_ = encode_pair _`(SUBST_ALL_TAC o SYM)
        \\ qpat_x_assum`homotopic _ (k o j -: _) _`mp_tac
        \\ simp[homotopic_id_map_agent_id]
        \\ strip_tac
        \\ pop_assum (fn th => simp[Once(GSYM th)])
        \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
        \\ simp[pre_chu_def, composable_in_def, restrict_def]
        \\ fs[maps_to_in_chu] )
      \\ simp[]
      \\ qpat_x_assum`k :- _ → _ -: _`mp_tac
      \\ simp[maps_to_in_chu, is_chu_morphism_def]
      \\ strip_tac
      \\ first_x_assum(fn th => DEP_REWRITE_TAC[(GSYM (Q.GEN`a`(Q.SPEC`a`th)))])
      \\ simp[Abbr`d'`, PULL_EXISTS, EXISTS_PROD, mk_cf_def] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu, Abbr`p`]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def,
              PULL_EXISTS, EXISTS_PROD]
      \\ simp[restrict_def]
      \\ `c'.agent = x ∧ m.agent = x ∧ m.env = IMAGE encode_pair (y × b') ∧
          c'.env = IMAGE encode_pair (y × z)` by simp[Abbr`c'`, Abbr`m`]
      \\ simp[PULL_EXISTS, EXISTS_PROD]
      \\ simp[Abbr`b'`]
      \\ `d'.env = z` by simp[Abbr`d'`]
      \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[Abbr`c'`, mk_cf_def]
      \\ simp[move_def, mk_cf_def]
      \\ rpt gen_tac \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ simp[Abbr`m`, mk_cf_def]
      \\ qpat_assum`k :- _ → _ -: _`mp_tac
      \\ simp_tac(srw_ss())[maps_to_in_chu, is_chu_morphism_def]
      \\ strip_tac
      \\ first_x_assum(fn th => DEP_REWRITE_TAC[(GSYM (Q.GEN`a`(Q.SPEC`a`th)))])
      \\ qpat_x_assum`homotopic _ (j o k -: _) _`mp_tac
      \\ simp[homotopic_id_map_env_id] \\ strip_tac
      \\ pop_assum mp_tac
      \\ disch_then drule
      \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
      \\ simp[pre_chu_def, composable_in_def, restrict_def]
      \\ fs[maps_to_in_chu]
      \\ simp[Abbr`d'`, PULL_EXISTS, EXISTS_PROD, mk_cf_def] )
    \\ rw[homotopic_id_map_agent_id]
    \\ TRY (irule maps_to_comp \\ simp[] \\ metis_tac[])
    \\ AP_TERM_TAC
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ simp[composable_in_def, pre_chu_def]
    \\ fs[maps_to_in_chu]
    \\ simp[restrict_def, Abbr`p`, Abbr`q`, mk_chu_morphism_def]
    \\ pop_assum mp_tac
    \\ rw[Abbr`m`, Abbr`c'`])
  \\ qexists_tac`m.agent`
  \\ qexists_tac`m.env`
  \\ qexists_tac`d.env`
  \\ qexists_tac`λx y z. d.eval (m.eval x y) z`
  \\ qmatch_goalsub_abbrev_tac`c ≃ c' -: w`
  \\ qmatch_goalsub_abbrev_tac`d ≃ d' -: w`
  \\ `c' = move d m`
  by (
    simp[cf_component_equality, Abbr`c'`]
    \\ simp[move_def, mk_cf_def]
    \\ conj_tac >- fs[chu_objects_def]
    \\ simp[EXISTS_PROD, FUN_EQ_THM]
    \\ rw[] \\ rw[] )
  \\ simp[]
  \\ reverse conj_tac
  >- (
    qpat_x_assum`m ∈ _`mp_tac
    \\ simp_tac std_ss [chu_objects_def, wf_def, finite_cf_def]
    \\ simp[] )
  \\ simp[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism d d' <|
       map_agent := λa. @b. b ∈ d'.agent ∧ UNCURRY m.eval (decode_pair b) = a;
       map_env := I |>`
  \\ qexists_tac`mk_chu_morphism d' d <|
       map_agent := UNCURRY m.eval o decode_pair;
       map_env := I |>`
  \\ qmatch_goalsub_abbrev_tac`p o q -: _`
  \\ `d' ∈ chu_objects w`
  by (
    simp[chu_objects_def, Abbr`d'`]
    \\ qpat_x_assum`_ ∈ _`mp_tac
    \\ qpat_x_assum`_ ∈ _`mp_tac
    \\ simp[chu_objects_def]
    \\ simp[wf_def, finite_cf_def]
    \\ simp[image_def, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
    \\ rw[] \\ metis_tac[] )
  \\ conj_asm1_tac
  >- (
    simp[Abbr`q`, maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ `d'.env = d.env` by simp[Abbr`d'`] \\ simp[]
    \\ simp[Abbr`d'`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ conj_asm1_tac
    >- (
      rw[]
      \\ SELECT_ELIM_TAC
      \\ simp[PULL_EXISTS]
      \\ fs[image_def, SET_EQ_SUBSET, SUBSET_DEF] )
    \\ simp[]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[] \\ strip_tac \\ simp[]
    \\ qpat_x_assum`_ = encode_pair _`mp_tac
    \\ SELECT_ELIM_TAC
    \\ simp[PULL_EXISTS]
    \\ fs[image_def, SET_EQ_SUBSET, SUBSET_DEF] )
  \\ conj_asm1_tac
  >- (
    simp[Abbr`p`, maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ `d'.env = d.env` by simp[Abbr`d'`] \\ simp[]
    \\ simp[Abbr`d'`, PULL_EXISTS, EXISTS_PROD, mk_cf_def]
    \\ fs[image_def, SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS] )
  \\ rw[homotopic_id_map_env_id]
  \\ TRY (irule maps_to_comp \\ simp[] \\ metis_tac[])
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ simp[composable_in_def, pre_chu_def]
  \\ fs[maps_to_in_chu]
  \\ simp[restrict_def, Abbr`p`, Abbr`q`, mk_chu_morphism_def]
  \\ pop_assum mp_tac
  \\ rw[Abbr`d'`]
QED

Theorem additive_subagent_categorical:
  additive_subagent c d ⇔
  let w = c.world in
  ∃m0. m0 :- c → d -: chu w ∧
    ∀m. m :- c → cfbot w w -: chu w ⇒
      ∃m1. m1 :- d → cfbot w w -: chu w ∧
        homotopic w m (m1 o m0 -: chu w)
Proof
  simp[additive_subagent_committing]
  \\ reverse eq_tac \\ strip_tac
  >- (
    qexists_tac`IMAGE m0.map.map_agent c.agent`
    \\ qexists_tac`d.agent`
    \\ qexists_tac`d.env`
    \\ qexists_tac`d.eval`
    \\ conj_tac
    >- (
      simp[SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
    \\ qmatch_goalsub_abbrev_tac `d ≃ d' -: w`
    \\ `c ∈ chu_objects w ∧ d ∈ chu_objects w`
    by metis_tac[maps_to_in_chu]
    \\ reverse conj_tac
    >- (
      `d' = d` suffices_by rw[]
      \\ rw[Abbr`d'`, cf_component_equality, mk_cf_def]
      \\ fs[chu_objects_def]
      \\ fs[wf_def]
      \\ rw[FUN_EQ_THM]
      \\ metis_tac[] )
    \\ qmatch_goalsub_abbrev_tac`c ≃ c' -: _`
    \\ simp[homotopy_equiv_def]
    \\ imp_res_tac in_chu_objects_finite_world
    \\ `∀e. e ∈ c.env ⇒ mk_chu_morphism c (cfbot w w)
          <| map_agent := flip c.eval e;
             map_env := K e |> :- c → cfbot w w -: chu w`
    by (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[cfbot_def]
      \\ simp[cf1_def, mk_cf_def]
      \\ qpat_x_assum`c ∈ _`mp_tac
      \\ simp[chu_objects_def, wf_def] )
    \\ fs[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
    \\ pop_assum mp_tac
    \\ qho_match_abbrev_tac`(∀e. e ∈ c.env ⇒ h e :- _ → _ -: _) ⇒ _`
    \\ strip_tac
    \\ qexists_tac`mk_chu_morphism c c' <| map_agent := m0.map.map_agent;
         map_env := m0.map.map_env |>`
    \\ qexists_tac`mk_chu_morphism c' c <| map_agent := λa. @b. b ∈ c.agent ∧ m0.map.map_agent b = a;
         map_env := λe. (f (h e)).map.map_env "" |>`
    \\ conj_asm1_tac
    >- (
      qpat_x_assum`m0 :- _ → _ -: _`mp_tac
      \\ simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[Abbr`c'`, mk_cf_def]
      \\ simp[restrict_def]
      \\ qpat_x_assum`d ∈ _`mp_tac
      \\ qpat_x_assum`c ∈ _`mp_tac
      \\ simp[chu_objects_def, wf_def]
      \\ simp[extensional_def]
      \\ simp[finite_cf_def]
      \\ metis_tac[IMAGE_FINITE] )
    \\ `c' ∈ chu_objects w` by metis_tac[maps_to_in_chu]
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[Abbr`c'`, PULL_EXISTS, mk_cf_def]
      \\ `"" ∈ (cfbot w w).env` by simp[cfbot_def]
      \\ conj_asm1_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ conj_tac >- metis_tac[]
      \\ rpt strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ qpat_assum`m0 :- c → _ -: _`mp_tac
      \\ simp_tac (srw_ss())[maps_to_in_chu, is_chu_morphism_def]
      \\ strip_tac
      \\ SELECT_ELIM_TAC
      \\ conj_tac >- metis_tac[]
      \\ qx_gen_tac`y` \\ strip_tac
      \\ pop_assum (assume_tac o SYM) \\ simp[]
      \\ first_x_assum(fn th => DEP_REWRITE_TAC[GSYM(Q.GEN`a`(Q.SPEC`a`th))])
      \\ conj_tac >- metis_tac[]
      \\ qmatch_goalsub_rename_tac`h e`
      \\ `homotopic w (h e) (f (h e) o m0 -: chu w)` by metis_tac[]
      \\ pop_assum mp_tac
      \\ simp_tac std_ss [homotopic_def, GSYM AND_IMP_INTRO]
      \\ ntac 4 (disch_then kall_tac)
      \\ simp_tac (srw_ss()) [pre_chu_def, GSYM AND_IMP_INTRO]
      \\ ntac 2 (disch_then kall_tac)
      \\ `(h e).dom = c` by metis_tac[maps_to_in_chu]
      \\ `(f (h e) o m0 -: chu w) :- c → cfbot w w -: chu w` by (
        irule maps_to_comp \\ simp[] \\ metis_tac[] )
      \\ `(f (h e) o m0 -: chu w).cod = cfbot w w` by metis_tac[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, hom_comb_def]
      \\ strip_tac
      \\ pop_assum mp_tac
      \\ simp[cfbot_def]
      \\ simp[cf1_def, mk_cf_def]
      \\ disch_then drule
      \\ `(cfbot w w).agent = w` by simp[cfbot_def]
      \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
      \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
      \\ `(f (h e)).cod = cfbot w w` by metis_tac[maps_to_in_chu]
      \\ simp[pre_chu_def, restrict_def, composable_in_def]
      \\ conj_tac >- metis_tac[maps_to_in_chu]
      \\ strip_tac
      \\ simp[Abbr`h`, mk_chu_morphism_def]
      \\ simp[restrict_def])
    \\ reverse conj_tac
    >- (
      rw[homotopic_id_map_agent_id]
      \\ TRY ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
      \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
      \\ simp[pre_chu_def, restrict_def, composable_in_def]
      \\ fs[maps_to_in_chu]
      \\ simp[mk_chu_morphism_def, restrict_def]
      \\ SELECT_ELIM_TAC
      \\ `c'.agent = IMAGE m0.map.map_agent c.agent` by simp[Abbr`c'`]
      \\ fs[] \\ metis_tac[] )
    \\ rw[homotopic_id_map_agent_id]
    \\ TRY ( irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ simp[FUN_EQ_THM]
    \\ qx_gen_tac`e`
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ simp[pre_chu_def, composable_in_def, restrict_def]
    \\ conj_asm1_tac >- metis_tac[maps_to_in_chu]
    \\ reverse(Cases_on`e ∈ c.env`)
    >- ( qpat_x_assum`c ∈ _`mp_tac \\ simp[chu_objects_def, wf_def] )
    \\ qpat_x_assum`_ ∧ _` strip_assume_tac
    \\ pop_assum mp_tac
    \\ simp[is_chu_morphism_def, GSYM AND_IMP_INTRO]
    \\ ntac 4 (disch_then kall_tac)
    \\ simp[AND_IMP_INTRO]
    \\ disch_then(fn th => DEP_REWRITE_TAC[GSYM th])
    \\ simp[Once mk_chu_morphism_def, restrict_def]
    \\ conj_tac >- simp[Abbr`c'`]
    \\ simp[Once mk_chu_morphism_def, restrict_def]
    \\ simp[Once mk_chu_morphism_def, restrict_def]
    \\ `"" ∈ (cfbot w w).env` by simp[cfbot_def]
    \\ simp[Abbr`c'`, mk_cf_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ pop_assum kall_tac
    \\ `is_chu_morphism d (cfbot w w) (f (h e)).map` by metis_tac[maps_to_in_chu]
    \\ pop_assum mp_tac
    \\ simp[is_chu_morphism_def]
    \\ strip_tac
    \\ pop_assum (fn th => DEP_REWRITE_TAC[th])
    \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ `homotopic w (f (h e) o m0 -: chu w) (h e)` by metis_tac[homotopic_sym]
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [homotopic_def, GSYM AND_IMP_INTRO]
    \\ ntac 4 (disch_then kall_tac)
    \\ simp[pre_chu_def, GSYM AND_IMP_INTRO]
    \\ ntac 2 (disch_then kall_tac)
    \\ `(h e).cod = cfbot w w` by metis_tac[maps_to_in_chu]
    \\ `(f (h e) o m0 -: chu w) :- c → cfbot w w -: chu w` by (
      irule maps_to_comp \\ simp[] \\ metis_tac[] )
    \\ `(f (h e) o m0 -: chu w).dom = c` by metis_tac[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, hom_comb_def]
    \\ strip_tac
    \\ pop_assum mp_tac
    \\ simp[cfbot_def]
    \\ simp[cf1_def, mk_cf_def]
    \\ disch_then drule
    \\ `(cfbot w w).agent = w` by simp[cfbot_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
    \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
    \\ `(f (h e)).cod = cfbot w w` by metis_tac[maps_to_in_chu]
    \\ simp[pre_chu_def, restrict_def, composable_in_def]
    \\ conj_tac >- metis_tac[maps_to_in_chu]
    \\ `m0.dom = c` by metis_tac[maps_to_in_chu]
    \\ simp[]
    \\ disch_then (assume_tac o SYM)
    \\ simp[]
    \\ simp[Abbr`h`, mk_chu_morphism_def]
    \\ simp[restrict_def])
  \\ qmatch_assum_abbrev_tac`c ≃ c' -: w`
  \\ qmatch_assum_abbrev_tac`d ≃ d' -: w`
  \\ fs[homotopy_equiv_def]
  \\ qmatch_assum_rename_tac`f1 :- c → c' -: _`
  \\ qmatch_assum_rename_tac`f2 :- c' → c -: _`
  \\ qmatch_assum_rename_tac`f3 :- d → d' -: _`
  \\ qmatch_assum_rename_tac`f4 :- d' → d -: _`
  \\ `c' ∈ chu_objects w ∧ d' ∈ chu_objects w` by metis_tac[maps_to_in_chu]
  \\ `mk_chu_morphism c' d' <| map_agent := I; map_env := I |> :- c' → d' -: chu w`
  by (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[Abbr`c'`, Abbr`d'`, mk_cf_def]
    \\ fs[SUBSET_DEF] )
  \\ qmatch_assum_abbrev_tac`f0 :- c' → d' -: _`
  \\ qexists_tac `f4 o f0 o f1 -: chu w -: chu w`
  \\ conj_tac
  >- (
    irule maps_to_comp \\ simp[]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule maps_to_comp \\ simp[]
    \\ metis_tac[] )
  \\ rpt strip_tac
  \\ qexists_tac`mk_chu_morphism d (cfbot w w) <|
       map_agent := flip d.eval (f3.map.map_env (f2.map.map_env (m.map.map_env "")));
       map_env := f3.map.map_env o f2.map.map_env o m.map.map_env |>`
  \\ `d ∈ chu_objects w` by metis_tac[maps_to_in_chu]
  \\ imp_res_tac in_chu_objects_finite_world
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_chu]
    \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
    \\ simp[restrict_def]
    \\ simp[cfbot_def]
    \\ `"" ∈ (cfbot w w).env` by simp[cfbot_def]
    \\ simp[cf1_def, mk_cf_def]
    \\ fs[chu_objects_def, wf_def]
    \\ `c'.env = z ∧ d'.env = z` by simp[Abbr`c'`, Abbr`d'`]
    \\ metis_tac[maps_to_in_chu, is_chu_morphism_def] )
  \\ qmatch_assum_abbrev_tac`g :- d → _ -: _`
  \\ qmatch_goalsub_abbrev_tac`homotopic w m n`
  \\ `n :- c → cfbot w w -: chu w`
  by (
    simp[Abbr`n`]
    \\ irule maps_to_comp \\ simp[]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule maps_to_comp \\ simp[]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule maps_to_comp \\ simp[]
    \\ metis_tac[] )
  \\ simp[homotopic_def, pre_chu_def]
  \\ simp[CONJ_ASSOC]
  \\ conj_tac >- fs[maps_to_in_chu]
  \\ simp[hom_comb_def]
  \\ simp[is_chu_morphism_def]
  \\ simp[CONJ_ASSOC]
  \\ conj_tac  >- ( fs[maps_to_in_chu] \\ fs[is_chu_morphism_def] )
  \\ `m.dom = c ∧ n.cod = cfbot w w` by fs[maps_to_in_chu] \\ simp[]
  \\ qpat_assum`m :- _ → _ -: _`mp_tac
  \\ simp_tac std_ss [maps_to_in_chu] \\ strip_tac
  \\ qpat_x_assum`is_chu_morphism _ _ _`mp_tac
  \\ simp[is_chu_morphism_def] \\ strip_tac
  \\ simp[Abbr`n`]
  \\ `f0 o f1 -: chu w :- c → d' -: chu w` by
    (irule maps_to_comp \\ simp[] \\ metis_tac[])
  \\ `f4 o f0 o f1 -: chu w -: chu w :- c → d -: chu w` by
    (irule maps_to_comp \\ simp[] \\ metis_tac[])
  \\ DEP_ONCE_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ conj_tac >- fs[composable_in_def, pre_chu_def, maps_to_in_chu]
  \\ `(f4 o f0 o f1 -: chu w -: chu w).dom = c ∧ g.cod = cfbot w w` by fs[maps_to_in_chu]
  \\ simp[pre_chu_def, restrict_def]
  \\ simp[Abbr`g`, mk_chu_morphism_def, restrict_def]
  \\ DEP_ONCE_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ conj_tac >- fs[composable_in_def, pre_chu_def, maps_to_in_chu]
  \\ `(f0 o f1 -: chu w).dom = c ∧ f4.cod = d` by fs[maps_to_in_chu]
  \\ simp[pre_chu_def, restrict_def]
  \\ rpt gen_tac \\ strip_tac
  \\ `c'.env = z ∧ d'.env = z` by simp[Abbr`c'`, Abbr`d'`]
  \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ DEP_ONCE_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ conj_tac >- fs[composable_in_def, pre_chu_def, maps_to_in_chu]
  \\ `f1.dom = c ∧ f0.cod = d'` by fs[maps_to_in_chu]
  \\ simp[pre_chu_def, restrict_def]
  \\ reverse IF_CASES_TAC >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ qpat_assum`f1 :- _ → _ -: _`mp_tac
  \\ simp_tac (srw_ss()) [maps_to_in_chu, is_chu_morphism_def]
  \\ strip_tac
  \\ first_assum(fn th => DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`th)])
  \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ simp[Abbr`f0`, mk_chu_morphism_def, restrict_def]
  \\ qpat_x_assum`homotopic _ (f3 o f4 -: _) _`mp_tac
  \\ simp[homotopic_id_map_env_id] \\ strip_tac
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ conj_tac >- fs[composable_in_def, pre_chu_def, maps_to_in_chu]
  \\ `f4.dom = d' ∧ f3.cod = d'` by fs[maps_to_in_chu]
  \\ simp[pre_chu_def, restrict_def]
  \\ `c'.agent = x` by simp[Abbr`c'`]
  \\ `f1.map.map_agent a ∈ x` by metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ `c'.eval (f1.map.map_agent a) = d'.eval (f1.map.map_agent a)`
  by ( fs[Abbr`c'`, Abbr`d'`, mk_cf_def, SUBSET_DEF] )
  \\ simp[]
  \\ disch_then(fn th => DEP_REWRITE_TAC[th])
  \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ qpat_assum`f2 :- _ → _ -: _`mp_tac
  \\ simp_tac (srw_ss()) [maps_to_in_chu, is_chu_morphism_def]
  \\ strip_tac
  \\ qpat_assum`_ = d'.eval _`(SUBST1_TAC o SYM)
  \\ first_assum(fn th => DEP_REWRITE_TAC[Q.GEN`a`(Q.SPEC`a`th)])
  \\ conj_tac >- metis_tac[maps_to_in_chu, is_chu_morphism_def]
  \\ qpat_x_assum`homotopic _ (f2 o f1 -: _) _`mp_tac
  \\ DEP_REWRITE_TAC[homotopic_id_map_agent_id]
  \\ conj_tac >- simp[] \\ strip_tac
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[compose_in_thm, compose_thm, chu_comp]
  \\ conj_tac >- fs[composable_in_def, pre_chu_def, maps_to_in_chu]
  \\ simp_tac(srw_ss())[pre_chu_def, restrict_def]
  \\ disch_then drule
  \\ reverse IF_CASES_TAC >- rfs[]
  \\ disch_then SUBST1_TAC
  \\ simp[]
QED

val _ = export_theory();
