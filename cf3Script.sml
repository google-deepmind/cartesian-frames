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
     pred_setTheory pairTheory categoryTheory
     cf0Theory cf1Theory cf2Theory

val _ = new_theory"cf3";

Theorem ensure_cf1_morphism:
  (s ∈ ensure c ⇔ s ⊆ c.world ∧ ∃m. is_chu_morphism (cf1 c.world s) c m)
Proof
  rw[ensure_def, is_chu_morphism_def]
  \\ Cases_on`s ⊆ c.world` \\ simp[]
  \\ simp[extensional_def, cf1_def, mk_cf_def]
  \\ rw[EQ_IMP_THM]
  >- (
    qexists_tac`<| map_agent := λx. if x = "" then a else ARB;
                   map_env := λe. if e ∈ c.env then c.eval a e else ARB |>`
    \\ rw[] \\ fs[SUBSET_DEF] \\ metis_tac[] )
  \\ qexists_tac`m.map_agent ""` \\ rw[]
  \\ metis_tac[]
QED

Theorem prevent_cf1_morphism:
  c ∈ chu_objects w ⇒
  (s ∈ prevent c ⇔ s ⊆ w ∧ ∃m. is_chu_morphism (cf1 w (w DIFF s)) c m)
Proof
  rw[chu_objects_def]
  \\ reverse(Cases_on`s ⊆ c.world` \\ simp[])
  >- simp[prevent_def]
  \\ `s ∈ prevent c ⇔ c.world DIFF s ∈ ensure c`
  by (
    rw[prevent_def, ensure_def]
    \\ fs[SUBSET_DEF, wf_def]
    \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ rw[ensure_cf1_morphism]
QED

Theorem ensure_morphism_mono:
  m :- c → d -: chu w ⇒ ensure c ⊆ ensure d
Proof
  rw[SUBSET_DEF]
  \\ fs[ensure_cf1_morphism]
  \\ qmatch_assum_rename_tac`is_chu_morphism _ c f1`
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ `w = c.world ∧ w = d.world` by fs[chu_objects_def]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ qabbrev_tac`m1 = <| dom := cf1 w x; cod := c; map := f1 |>`
  \\ `m1 :- cf1 w x → c -: chu w`
  by ( simp[maps_to_in_def, Abbr`m1`] \\ fs[pre_chu_def] \\ rfs[])
  \\ `m o m1 -: chu w :- cf1 w x → d -: chu w` by (
    imp_res_tac maps_to_comp \\ fs[] )
  \\ fs[maps_to_in_def, pre_chu_def]
  \\ metis_tac[]
QED

Theorem ensure_prod:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  (ensure (c && d) = ensure c ∩ ensure d)
Proof
  strip_tac
  \\ simp[EXTENSION]
  \\ simp[ensure_cf1_morphism]
  \\ gen_tac
  \\ `c.world = w ∧ d.world = w` by fs[chu_objects_def]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ Cases_on`x ⊆ c.world` \\ rfs[]
  \\ simp[EQ_IMP_THM]
  \\ conj_tac
  >- (
    strip_tac
    \\ `<| dom := cf1 w x; cod := c && d; map := m|> :- cf1 w x → c && d -: chu w`
    by ( simp[maps_to_in_def, pre_chu_def] )
    \\ qspecl_then[`c`,`d`]mp_tac(Q.GENL[`a`,`b`]proj_maps_to)
    \\ impl_tac >- simp[] \\ strip_tac
    \\ imp_res_tac maps_to_comp
    \\ rpt(first_x_assum(qspec_then`ARB`kall_tac)) \\ fs[]
    \\ fs[maps_to_in_def, pre_chu_def]
    \\ metis_tac[] )
  \\ simp[PULL_EXISTS]
  \\ qx_genl_tac[`m1`,`m2`]
  \\ strip_tac
  \\ `<| dom := cf1 w x; cod := c; map := m1|> :- cf1 w x → c -: chu w`
  by ( simp[maps_to_in_def, pre_chu_def] )
  \\ `<| dom := cf1 w x; cod := d; map := m2|> :- cf1 w x → d -: chu w`
  by ( simp[maps_to_in_def, pre_chu_def] )
  \\ `∃p. p :- cf1 w x → c && d -: chu w` by metis_tac[prod_is_prod, EXISTS_UNIQUE_THM]
  \\ fs[maps_to_in_def, pre_chu_def]
  \\ metis_tac[]
QED

Theorem ensure_sum:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ∧ c ≠ null w ∧ d ≠ null w ⇒
  ensure (sum c d) = ensure c ∪ ensure d
Proof
  strip_tac
  \\ Cases_on`c.env = ∅`
  >- (
    Cases_on`c.agent = ∅`
    >- (
      `c = null w` by (
        simp_tac std_ss [cf_component_equality]
        \\ simp[null_def]
        \\ fs[chu_objects_def, wf_def]
        \\ simp[FUN_EQ_THM] )
      \\ fs[] )
    \\ `ensure c ∪ ensure d = POW w`
    by (
      simp[EXTENSION, IN_POW]
      \\ simp[ensure_def]
      \\ fs[chu_objects_def]
      \\ metis_tac[MEMBER_NOT_EMPTY] )
    \\ `ensure (sum c d) = POW w`
    by (
      simp[EXTENSION, IN_POW]
      \\ simp[ensure_def, PULL_EXISTS]
      \\ simp[sum_def]
      \\ fs[chu_objects_def]
      \\ metis_tac[MEMBER_NOT_EMPTY] )
    \\ simp[] )
  \\ Cases_on`d.env = ∅`
  >- (
    Cases_on`d.agent = ∅`
    >- (
      `d = null w` by (
        simp_tac std_ss [cf_component_equality]
        \\ simp[null_def]
        \\ fs[chu_objects_def, wf_def]
        \\ simp[FUN_EQ_THM] )
      \\ fs[] )
    \\ `ensure c ∪ ensure d = POW w`
    by (
      simp[EXTENSION, IN_POW]
      \\ simp[ensure_def]
      \\ fs[chu_objects_def]
      \\ metis_tac[MEMBER_NOT_EMPTY] )
    \\ `ensure (sum c d) = POW w`
    by (
      simp[EXTENSION, IN_POW]
      \\ simp[ensure_def, PULL_EXISTS]
      \\ simp[sum_def]
      \\ fs[chu_objects_def]
      \\ metis_tac[MEMBER_NOT_EMPTY] )
    \\ simp[] )
  \\ once_rewrite_tac[SET_EQ_SUBSET]
  \\ `c.world = w ∧ d.world = w ∧ (sum c d).world = w`
  by ( simp[sum_def] \\ fs[chu_objects_def] )
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ reverse conj_tac
  >- (
    simp[Once SUBSET_DEF, ensure_cf1_morphism]
    \\ simp[Once SUBSET_DEF, SimpR``(/\)``]
    \\ simp[ensure_cf1_morphism]
    \\ conj_tac \\ gen_tac \\ strip_tac
    \\ pop_assum(mp_then Any mp_tac is_chu_morphism_maps_to)
    \\ disch_then(qspec_then`w`mp_tac) \\ simp[] \\ strip_tac
    \\ metis_tac[cf1_in_chu_objects, inj_maps_to, maps_to_comp,
                 is_category_chu, maps_to_in_chu] )
  \\ simp[SUBSET_DEF]
  \\ simp[ensure_cf1_morphism]
  \\ gen_tac \\ strip_tac
  \\ fs[is_chu_morphism_def, extensional_def]
  \\ qpat_x_assum`_ ∈ _.agent`mp_tac
  \\ simp[Once sum_def]
  \\ simp[PULL_EXISTS]
  \\ strip_tac
  \\ qmatch_assum_rename_tac`z ∈ _.agent`
  >- (
    disj1_tac
    \\ fs[sum_def, mk_cf_def, EXISTS_PROD, sum_eval_def, PULL_EXISTS]
    \\ qexists_tac`<| map_agent := restrict (K z) {""};
                      map_env := restrict (m.map_env o (λp1. encode_pair (p1, CHOICE d.env))) c.env |>`
    \\ simp[restrict_def]
    \\ metis_tac[CHOICE_DEF])
  \\ disj2_tac
  \\ fs[sum_def, mk_cf_def, EXISTS_PROD, sum_eval_def, PULL_EXISTS]
  \\ qexists_tac`<| map_agent := restrict (K z) {""};
                    map_env := restrict (m.map_env o (λp2. encode_pair (CHOICE c.env, p2))) d.env |>`
  \\ simp[restrict_def]
  \\ metis_tac[CHOICE_DEF]
QED

Theorem ensure_sum_null:
  c.world = w ∧ c.agent ≠ ∅ ⇒
  ensure (sum (null w) c) = POW w
Proof
  rw[GSYM MEMBER_NOT_EMPTY, ensure_def, sum_def]
  \\ rw[EXTENSION, IN_POW]
QED

Theorem homotopy_equiv_ensure:
  c ≃ d -: w  ⇒ ensure c = ensure d
Proof
  rw[homotopy_equiv_def]
  \\ simp[EXTENSION, ensure_cf1_morphism]
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ `c.world = w ∧ d.world = w` by fs[chu_objects_def] \\ fs[]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ gen_tac \\ EQ_TAC \\ strip_tac \\ simp[]
  \\ pop_assum(mp_then Any (qspec_then`w`mp_tac) is_chu_morphism_maps_to)
  \\ simp[]
  \\ metis_tac[maps_to_in_chu, maps_to_comp, cf1_in_chu_objects, is_category_chu]
QED

Theorem ensure_prevent_swap_disjoint:
  DISJOINT (ensure c) (prevent (swap c))
Proof
  rw[ensure_def, prevent_def, IN_DISJOINT]
  \\ metis_tac[]
QED

Definition cf2_def:
  cf2 w s = sum (cf1 w s) (cf1 w (w DIFF s))
End

(* TODO: example of cf2 for a particular w and s *)

Theorem ctrl_cf2_morphism:
  c ∈ chu_objects w ⇒
  (s ∈ ctrl c ⇔ s ⊆ w ∧ ∃m. is_chu_morphism (cf2 w s) c m)
Proof
  rw[ctrl_def, ensure_cf1_morphism]
  \\ rw[UNDISCH prevent_cf1_morphism]
  \\ `c.world = w` by fs[chu_objects_def] \\ fs[]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ simp[cf2_def]
  \\ Cases_on`s ⊆ w` \\ simp[]
  \\ EQ_TAC \\ strip_tac
  \\ rpt(first_x_assum(mp_then (Pos(el 3)) (qspec_then`w`mp_tac) is_chu_morphism_maps_to))
  \\ simp[]
  \\ PROVE_TAC[sum_is_sum, inj_maps_to, cf1_in_chu_objects, DIFF_SUBSET,
               is_category_chu, EXISTS_UNIQUE_THM, maps_to_comp, maps_to_in_chu]
QED

Theorem prevent_ensure_compl:
  c ∈ chu_objects w ∧ s ⊆ w ⇒ (s ∈ prevent c ⇔ w DIFF s ∈  ensure c)
Proof
  rw[prevent_def, chu_objects_def, wf_def, ensure_def, SUBSET_DEF]
  \\ metis_tac[]
QED

Theorem ctrl_ensure_compl:
  c ∈ chu_objects w ⇒
  (s ∈ ctrl c ⇔ s ∈ ensure c ∧ (w DIFF s) ∈ ensure c)
Proof
  rw[ctrl_def]
  \\ reverse(Cases_on`s ⊆ w`) >- fs[ensure_def, chu_objects_def]
  \\ metis_tac[prevent_ensure_compl]
QED

Theorem ctrl_morphism_mono:
  m :- c → d -: chu w ⇒ ctrl c ⊆ ctrl d
Proof
  rw[SUBSET_DEF]
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ rpt(first_x_assum (mp_then Any strip_assume_tac ctrl_ensure_compl))
  \\ fs[]
  \\ imp_res_tac ensure_morphism_mono
  \\ fs[SUBSET_DEF]
QED

Theorem ctrl_prod:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  ctrl (c && d) = ctrl c ∩ ctrl d
Proof
  rw[EXTENSION]
  \\ last_assum (mp_then Any (first_assum o mp_then Any strip_assume_tac) prod_in_chu_objects)
  \\ EVERY_ASSUM (mp_then Any strip_assume_tac ctrl_ensure_compl)
  \\ fs[]
  \\ DEP_REWRITE_TAC[ensure_prod]
  \\ simp[]
  \\ metis_tac[]
QED

Theorem homotopy_equiv_ctrl:
  c ≃ d -: w ⇒ ctrl c = ctrl d
Proof
  rw[EXTENSION]
  \\ `c ∈ chu_objects w ∧ d ∈ chu_objects w` by (
    fs[homotopy_equiv_def]
    \\ imp_res_tac maps_to_obj
    \\ fs[] )
  \\ DEP_REWRITE_TAC[ctrl_ensure_compl]
  \\ simp[]
  \\ metis_tac[homotopy_equiv_ensure]
QED

Theorem obs_homotopy_equiv:
  c ≃ d -: w ⇒ obs c = obs d
Proof
  `∀c d. c ≃ d -: w ⇒ obs c ⊆ obs d`
    suffices_by metis_tac[homotopy_equiv_sym, SET_EQ_SUBSET]
  \\ rw[homotopy_equiv_def, SUBSET_DEF]
  \\ fs[obs_def]
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ `c.world = w ∧ d.world = w` by fs[chu_objects_def] \\ fs[]
  \\ rpt gen_tac \\ strip_tac
  \\ first_x_assum(qspecl_then[`g.map.map_agent a0`,`g.map.map_agent a1`]mp_tac)
  \\ impl_keep_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
  \\ disch_then(qx_choose_then`a`strip_assume_tac)
  \\ qexists_tac`f.map.map_agent a`
  \\ fs[ifs_def]
  \\ conj_asm1_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
  \\ qx_gen_tac`e` \\ strip_tac
  \\ first_x_assum(qspec_then`f.map.map_env e`mp_tac)
  \\ impl_keep_tac >- fs[maps_to_in_chu, is_chu_morphism_def]
  \\ strip_tac
  \\ qabbrev_tac`fA = f.map.map_agent`
  \\ qabbrev_tac`fE = f.map.map_env`
  \\ qabbrev_tac`gA = g.map.map_agent`
  \\ qabbrev_tac`gE = g.map.map_env`
  \\ rpt(qhdtm_x_assum`homotopic`mp_tac)
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ simp[homotopic_def, pre_chu_def]
  \\ imp_res_tac (#1(EQ_IMP_RULE maps_to_in_chu)) \\ fs[]
  \\ simp[hom_comb_def]
  \\ simp[chu_id_morphism_map_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ simp[composable_in_def, pre_chu_def]
  \\ simp[is_chu_morphism_def]
  \\ strip_tac
  \\ pop_assum(strip_assume_tac o GSYM)
  \\ strip_tac
  \\ pop_assum(strip_assume_tac o GSYM)
  \\ fs[restrict_def]
  \\ qhdtm_x_assum`is_chu_morphism`mp_tac
  \\ qhdtm_x_assum`is_chu_morphism`mp_tac
  \\ simp[is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem image_compl_obs_prod:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ s ⊆ w ∧
  image c1 ⊆ s ∧ image c2 ⊆ w DIFF s ⇒ s ∈ obs (c1 && c2)
Proof
  rw[obs_def]
  >- fs[chu_objects_def]
  \\ simp[ifs_def]
  \\ qexists_tac`encode_pair (FST(decode_pair a0), SND(decode_pair a1))`
  \\ conj_asm1_tac >- fs[prod_def]
  \\ gen_tac
  \\ simp[Once prod_def, PULL_EXISTS]
  \\ fs[image_def, SUBSET_DEF, PULL_EXISTS]
  \\ pop_assum mp_tac
  \\ simp[prod_def, mk_cf_def, EXISTS_PROD, PULL_EXISTS]
  \\ strip_tac
  \\ simp[sum_eval_def]
  \\ strip_tac \\ rw[]
  \\ rfs[prod_def, EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem obs_homotopy_equiv_prod:
  c ∈ chu_objects w ⇒
  (s ∈ obs c ⇔ s ⊆ w ∧
   ∃c1 c2. c1 ∈ chu_objects w ∧
           c2 ∈ chu_objects w ∧
           image c1 ⊆ s ∧ image c2 ⊆ w DIFF s ∧
           c ≃ c1 && c2 -: w)
Proof
  strip_tac
  \\ EQ_TAC
  >- (
    strip_tac
    \\ qabbrev_tac`c1 = mk_cf (c with env := env_for c s)`
    \\ qabbrev_tac`c2 = mk_cf (c with env := env_for c (w DIFF s))`
    \\ `c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w`
    by (
      fs[chu_objects_def, Abbr`c1`, Abbr`c2`]
      \\ fs[wf_def, finite_cf_def]
      \\ simp[env_for_def, image_def, SUBSET_DEF, PULL_EXISTS])
    \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
    \\ conj_asm1_tac
    >- ( fs[obs_def, chu_objects_def] \\ rfs[] )
    \\ map_every qexists_tac[`c1`,`c2`] \\ simp[]
    \\ conj_asm1_tac
    >- (simp[image_def, Abbr`c1`, SUBSET_DEF, PULL_EXISTS, mk_cf_def, env_for_def])
    \\ conj_asm1_tac
    >- (simp[image_def, Abbr`c2`, SUBSET_DEF, PULL_EXISTS, mk_cf_def, env_for_def]
        \\ fs[chu_objects_def, wf_def])
    \\ Cases_on`c.agent = ∅`
    >- (
      `c1 = c2 ∧ c2 = c`
      by (
        simp[Abbr`c1`,Abbr`c2`,mk_cf_def, env_for_def]
        \\ fs[chu_objects_def, wf_def]
        \\ simp[cf_component_equality, FUN_EQ_THM])
      \\ simp[]
      \\ Cases_on`c.env = ∅`
      >- (
        `c = null w` by (
          simp[null_def, cf_component_equality]
          \\ fs[chu_objects_def, wf_def]
          \\ simp[FUN_EQ_THM] )
        \\ simp[] )
      \\ `c ≃ cf0 w -: w` by metis_tac[empty_agent_nonempty_env]
      \\ `c ≃ cf0 w && cf0 w -: w` by metis_tac[cf0_prod_cf0, homotopy_equiv_trans, homotopy_equiv_sym]
      \\ `c && c ≃ cf0 w && cf0 w -: w` by metis_tac[homotopy_equiv_prod, cf0_in_chu_objects]
      \\ metis_tac[homotopy_equiv_trans, homotopy_equiv_sym] )
    \\ simp[homotopy_equiv_def]
    \\ qexists_tac`mk_chu_morphism c (c1 && c2)
                     <| map_agent := W (CURRY encode_pair);
                        map_env := λe. sum_CASE (decode_sum e) I I |>`
    \\ qexists_tac`mk_chu_morphism (c1 && c2) c
                     <| map_agent := λp. @a. a ∈ UNCURRY (ifs c s) (decode_pair p);
                        map_env := λe. encode_sum ((if e ∈ c1.env then INL else INR) e) |>`
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[prod_def, PULL_EXISTS, mk_cf_def]
      \\ simp[Abbr`c1`, Abbr`c2`, mk_cf_def, PULL_EXISTS, env_for_def]
      \\ rw[] \\ rw[]
      \\ rw[sum_eval_def] )
    \\ `(c1 && c2).env = IMAGE (encode_sum o (λe. (if e ∈ env_for c s then INL else INR) e)) c.env`
    by (
      simp[Abbr`c1`, Abbr`c2`, prod_def, mk_cf_def, IMAGE_COMPOSE]
      \\ rewrite_tac[GSYM IMAGE_UNION]
      \\ AP_TERM_TAC
      \\ imp_res_tac env_for_compl_disjoint
      \\ pop_assum(qspec_then`s`mp_tac)
      \\ simp[IN_DISJOINT]
      \\ simp[EXTENSION, PULL_EXISTS]
      \\ `∀s e. e ∈ env_for c s ⇒ e ∈ c.env` by simp[env_for_def]
      \\ `wf c ∧ c.world = w` by fs[chu_objects_def]
      \\ metis_tac[obs_env_for] )
    \\ conj_asm1_tac
    >- (
      simp[maps_to_in_chu]
      \\ simp[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ simp[GSYM FORALL_AND_THM]
      \\ simp[PULL_FORALL]
      \\ rpt gen_tac
      \\ conj_tac >- (simp[Abbr`c1`] \\ metis_tac[])
      \\ Cases_on`a ∈ (c1 && c2).agent` \\ simp[]
      \\ SELECT_ELIM_TAC
      \\ pop_assum mp_tac
      \\ simp[Once prod_def, EXISTS_PROD]
      \\ strip_tac \\ simp[]
      \\ conj_tac >- fs[obs_def, Abbr`c1`, Abbr`c2`]
      \\ simp[prod_def, mk_cf_def, Abbr`c1`, Abbr`c2`]
      \\ rw[] \\ rfs[] \\ fs[] \\ rw[]
      \\ fs[ifs_def]
      \\ rw[sum_eval_def]
      \\ TRY(fs[env_for_def] \\ NO_TAC)
      \\ imp_res_tac env_for_compl_disjoint
      \\ pop_assum(qspec_then`s`mp_tac)
      \\ simp[IN_DISJOINT]
      \\ fs[chu_objects_def]
      \\ metis_tac[obs_env_for])
    \\ qmatch_abbrev_tac`homotopic w (f o g -: _) _ ∧ homotopic w (g o f -: _) _`
    \\ imp_res_tac maps_to_comp \\ fs[]
    \\ imp_res_tac (#1(EQ_IMP_RULE maps_to_in_chu))
    \\ simp[homotopic_def, pre_chu_def]
    \\ simp[hom_comb_def, chu_id_morphism_map_def]
    \\ qpat_x_assum`is_chu_morphism _ _ (_ o _ -: _).map`mp_tac
    \\ qpat_x_assum`is_chu_morphism _ _ (_ o _ -: _).map`mp_tac
    \\ DEP_REWRITE_TAC[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ simp[composable_in_def, pre_chu_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[restrict_def]
    \\ ntac 2 strip_tac
    \\ conj_tac
    >- (
      simp[Abbr`f`,Abbr`g`,mk_chu_morphism_def,restrict_def]
      \\ simp[prod_def]
      \\ rpt gen_tac
      \\ strip_tac
      \\ SELECT_ELIM_TAC
      \\ simp[ifs_def]
      \\ conj_tac >- metis_tac[]
      \\ simp[Abbr`c1`, Abbr`c2`]
      \\ metis_tac[] )
    \\ rpt gen_tac
    \\ strip_tac
    \\ simp[Abbr`g`, Abbr`f`, mk_chu_morphism_def, restrict_def]
    \\ SELECT_ELIM_TAC
    \\ conj_tac
    >- (
      qpat_x_assum`a ∈ _`mp_tac
      \\ simp[prod_def, EXISTS_PROD]
      \\ strip_tac
      \\ simp[]
      \\ qpat_x_assum`_ ∈ obs _`mp_tac
      \\ simp[obs_def]
      \\ fs[Abbr`c1`, Abbr`c2`] )
    \\ gen_tac
    \\ qpat_x_assum`a ∈ _`mp_tac
    \\ simp[Once prod_def, EXISTS_PROD]
    \\ strip_tac \\ simp[]
    \\ simp[ifs_def]
    \\ strip_tac
    \\ simp[prod_def, mk_cf_def, Abbr`c1`, Abbr`c2`, PULL_EXISTS, EXISTS_PROD]
    \\ rw[] \\ rw[sum_eval_def] \\ qpat_x_assum`(COND _ _ _) _ = _`mp_tac \\ rw[]
    \\ TRY(fs[env_for_def] \\ NO_TAC)
    \\ fs[chu_objects_def]
    \\ metis_tac[obs_env_for] )
  \\ strip_tac
  \\ `s ∈ obs (c1 && c2)` by metis_tac[image_compl_obs_prod]
  \\ metis_tac[obs_homotopy_equiv]
QED

Theorem prod_ensure_prevent_equiv_cfT:
  c ∈ chu_objects w ∧ c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ s ⊆ w ∧
  c ≃ c1 && c2 -: w ∧ image c1 ⊆ s ∧ image c2 ⊆ w DIFF s ⇒
    (s ∈ prevent c ⇒ c1 ≃ cfT w -: w) ∧
    (s ∈ ensure c ⇒ c2 ≃ cfT w -: w)
Proof
  qho_match_abbrev_tac `P c c1 c2 s ⇒ Q c c1 c2 s ∧ R c c1 c2 s`
  \\ `∀c c1 c2 s. P c c1 c2 s ⇒ R c c1 c2 s` suffices_by (
    simp[Abbr`P`, Abbr`R`, Abbr`Q`]
    \\ reverse(rw[]) \\ first_x_assum irule \\ simp[]
    >- metis_tac[]
    \\ qexists_tac`c`
    \\ qexists_tac`c2`
    \\ qexists_tac`w DIFF s`
    \\ simp[GSYM prevent_ensure_compl]
    \\ simp[DIFF_DIFF_SUBSET]
    \\ metis_tac[homotopy_equiv_trans, prod_comm, iso_homotopy_equiv] )
  \\ rw[Abbr`P`, Abbr`R`, Abbr`Q`]
  \\ rfs[ensure_cf1_morphism]
  \\ `c.world = w` by fs[chu_objects_def]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ first_assum(mp_then Any (qspec_then`w`mp_tac) is_chu_morphism_maps_to)
  \\ simp[] \\ strip_tac
  \\ `∃f. f :- c → c1 && c2 -: chu w` by metis_tac[homotopy_equiv_def]
  \\ last_assum(mp_then Any mp_tac maps_to_comp)
  \\ simp[]
  \\ disch_then(first_assum o mp_then Any strip_assume_tac)
  \\ first_assum(mp_then Any (qspecl_then[`proj2 c1 c2`,`c2`]mp_tac) maps_to_comp)
  \\ simp[] \\ strip_tac
  \\ first_assum(mp_then Any mp_tac (#1(EQ_IMP_RULE(maps_to_in_chu))))
  \\ qmatch_goalsub_abbrev_tac`is_chu_morphism _ _ g.map`
  \\ simp[is_chu_morphism_def] \\ strip_tac
  \\ reverse(Cases_on`c2.env = ∅`)
  >- (
    fs[GSYM MEMBER_NOT_EMPTY]
    \\ `c2.eval (g.map.map_agent "") x ∈ w DIFF s`
    by ( fs[image_def, SUBSET_DEF] \\ metis_tac[] )
    \\ `(cf1 w s).eval "" (g.map.map_env x) ∈ s`
    by ( rewrite_tac[cf1_def] \\ simp[mk_cf_def] )
    \\ metis_tac[IN_DIFF] )
  \\ `c2.agent ≠ ∅` by metis_tac[MEMBER_NOT_EMPTY]
  \\ metis_tac[empty_env_nonempty_agent]
QED

Theorem cfT_ctrl_obs_disjoint:
  c ∈ chu_objects w ∧ ¬(c ≃ cfT w -: w) ⇒ DISJOINT (ctrl c) (obs c)
Proof
  CCONTR_TAC \\ fs[IN_DISJOINT]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ fs[UNDISCH(obs_homotopy_equiv_prod)]
  \\ fs[ctrl_def]
  \\ `c1 ≃ cfT w -: w ∧ c2 ≃ cfT w -: w` by metis_tac[prod_ensure_prevent_equiv_cfT]
  \\ PROVE_TAC[homotopy_equiv_prod, homotopy_equiv_trans,
               iso_homotopy_equiv, prod_cfT, cfT_in_chu_objects]
QED

Theorem image_subset_ensure_inter_obs_alt:
  c ∈ chu_objects w ∧ s ∈ ensure c ∩ obs c ⇒ image c ⊆ s
Proof
  rw[]
  \\ `FINITE w` by metis_tac[in_chu_objects_finite_world]
  \\ fs[UNDISCH(obs_homotopy_equiv_prod)]
  \\ `c2 ≃ cfT w -: w` by metis_tac[prod_ensure_prevent_equiv_cfT]
  \\ `c ≃ c1 -: w` by metis_tac[homotopy_equiv_trans, prod_cfT,
                                homotopy_equiv_prod, iso_homotopy_equiv,
                                cfT_in_chu_objects, homotopy_equiv_refl]
  \\ metis_tac[homotopy_equiv_image]
QED

val _ = export_theory();
