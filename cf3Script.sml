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
  \\ qabbrev_tac`m1 = <| dom := cf1 w x; cod := c; map := f1 |>`
  \\ `m1 :- cf1 w x → c -: chu w`
  by ( simp[maps_to_in_def, Abbr`m1`] \\ fs[pre_chu_def] )
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

(* TODO: prove counterxample ensure_sum if c or d is null? *)

Theorem homotopy_equiv_ensure:
  c ≃ d -: w  ⇒ ensure c = ensure d
Proof
  rw[homotopy_equiv_def]
  \\ simp[EXTENSION, ensure_cf1_morphism]
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ `c.world = w ∧ d.world = w` by fs[chu_objects_def] \\ fs[]
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
  \\ simp[cf2_def]
  \\ Cases_on`s ⊆ w` \\ simp[]
  \\ EQ_TAC \\ strip_tac
  \\ rpt(first_x_assum(mp_then (Pos(el 3)) (qspec_then`w`mp_tac) is_chu_morphism_maps_to))
  \\ simp[]
  \\ PROVE_TAC[sum_is_sum, inj_maps_to, cf1_in_chu_objects, DIFF_SUBSET,
               is_category_chu, EXISTS_UNIQUE_THM, maps_to_comp, maps_to_in_chu]
QED

Theorem ctrl_ensure_compl:
  c ∈ chu_objects w ⇒
  (s ∈ ctrl c ⇔ s ∈ ensure c ∧ (w DIFF s) ∈ ensure c)
Proof
  rw[ctrl_def, prevent_def]
  \\ rw[ensure_def]
  \\ fs[chu_objects_def]
  \\ fs[wf_def, SUBSET_DEF]
  \\ metis_tac[]
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

val _ = export_theory();
