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
     pred_setTheory helperSetTheory pairTheory relationTheory listTheory sortingTheory stringTheory
     categoryTheory cf0Theory matrixTheory cf1Theory

val _ = new_theory"cf2";

(* -- *)
Theorem IMAGE_CHR_UNIV:
  UNIV = IMAGE CHR (count 256)
Proof
  rw[EXTENSION]
  \\ Cases_on`x`
  \\ metis_tac[]
QED

Theorem FINITE_UNIV_char[simp]:
  FINITE (UNIV:char set)
Proof
  simp[IMAGE_CHR_UNIV]
QED

Theorem FINITE_strings_same_length:
  (∀x. x ∈ s ⇒ LENGTH x = m) ⇒ FINITE (s:string set)
Proof
  qid_spec_tac`s`
  \\ Induct_on`m` \\ rw[]
  >- (
    Cases_on`s` \\ fs[]
    \\ `x = ""` by metis_tac[] \\ rw[]
    \\ Cases_on`t` \\ fs[] \\ metis_tac[] )
  \\ `s ⊆ BIGUNION (IMAGE (λf. IMAGE (f o TL) s) (IMAGE CONS UNIV))`
  by (
    rw[SUBSET_DEF, PULL_EXISTS]
    \\ res_tac
    \\ Cases_on`x` \\ fs[]
    \\ qexists_tac`h::t` \\ simp[] )
  \\ match_mp_tac (MP_CANON SUBSET_FINITE)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ match_mp_tac FINITE_BIGUNION
  \\ simp[PULL_EXISTS]
  \\ gen_tac
  \\ simp[IMAGE_COMPOSE]
  \\ first_x_assum match_mp_tac
  \\ qx_gen_tac`z`
  \\ rw[PULL_EXISTS]
  \\ res_tac
  \\ Cases_on`x` \\ fs[]
QED

Theorem RC_char_lt:
  RC (char_lt) = char_le
Proof
  rw[FUN_EQ_THM, RC_DEF, char_le_def, char_lt_def, arithmeticTheory.LESS_OR_EQ]
  \\ metis_tac[ORD_11]
QED

Theorem WF_char_lt[simp]:
  WF char_lt
Proof
  rw[WF_DEF]
  \\ qexists_tac`CHR (LEAST n. (n < 256) ∧ B (CHR n))`
  \\ numLib.LEAST_ELIM_TAC
  \\ conj_tac >- (Cases_on`w` \\ fs[] \\ metis_tac[])
  \\ rw[] \\ Cases_on`b` \\ fs[char_lt_def] \\ rfs[]
QED

Theorem string_lt_LLEX:
  string_lt = LLEX char_lt
Proof
  simp[FUN_EQ_THM]
  \\ recInduct string_lt_ind
  \\ rw[string_lt_def]
QED

Theorem not_WF_string_lt:
  ¬WF string_lt
Proof
  rw[string_lt_LLEX]
  \\ match_mp_tac LLEX_not_WF
  \\ qexists_tac`CHR 0`
  \\ qexists_tac`CHR 1`
  \\ simp[char_lt_def]
QED

Theorem RC_REFL[simp]:
  RC R x x
Proof
  rw[RC_DEF]
QED

Theorem BIJ_restrict:
  BIJ (restrict f s) s t ⇔ BIJ f s t
Proof
  rw[BIJ_IFF_INV, restrict_def]
  \\ rw[EQ_IMP_THM]
  \\ metis_tac[]
QED

Theorem iso_objs_refl[simp]:
  is_category c ∧ x ∈ c.obj ⇒ x ≅ x -: c
Proof
  rw[iso_objs_def]
  \\ rw[iso_pair_between_objs_def, iso_pair_def]
  \\ metis_tac[id_comp_id, id_composable_id, id_dom_cod]
QED

Theorem iso_objs_trans:
  is_category c ∧
  x ≅ y -: c ∧ y ≅ z -: c ⇒ x ≅ z -: c
Proof
  simp[iso_objs_def, PULL_EXISTS]
  \\ qx_genl_tac[`f`,`g`,`h`,`i`]
  \\ strip_tac
  \\ fs[iso_pair_between_objs_def, iso_pair_def]
  \\ qexists_tac`h o f -: c`
  \\ qexists_tac`g o i -: c`
  \\ `f ≈> h -: c` by fs[composable_in_def]
  \\ `g ≈> f -: c` by (
    imp_res_tac composable_obj
    \\ rfs[compose_in_thm]
    \\ rfs[composable_in_def, compose_in_thm, morphism_component_equality] )
  \\ `i ≈> h -: c` by (
    imp_res_tac composable_obj
    \\ rfs[compose_in_thm]
    \\ rfs[composable_in_def, compose_in_thm, morphism_component_equality] )
  \\ `i ≈> g -: c` by fs[composable_in_def]
  \\ conj_asm1_tac >- simp[compose_in_thm]
  \\ conj_asm1_tac >- imp_res_tac composable_comp
  \\ `(h o f -:c) o g o i -:c -: c = (h o (f o g -: c) -:c) o i -: c`
  by ( DEP_REWRITE_TAC[comp_assoc] \\ rfs[compose_in_thm, composable_in_def] )
  \\ pop_assum SUBST1_TAC
  \\ `(g o i -:c) o h o f -:c -: c = (g o (i o h -: c) -:c) o f -: c`
  by (
    DEP_REWRITE_TAC[comp_assoc]
    \\ simp[]
    \\ imp_res_tac composable_obj
    \\ imp_res_tac composable_in_def
    \\ fs[] \\ rfs[]
    \\ simp[composable_in_def] )
  \\ pop_assum SUBST1_TAC
  \\ simp[]
  \\ DEP_REWRITE_TAC[id_comp1]
  \\ simp[]
  \\ imp_res_tac composable_in_def
  \\ simp[compose_in_thm, compose_thm]
  \\ fs[]
QED

Theorem HD_QSORT_SET_TO_LIST_IN[simp]:
  FINITE s ∧ s ≠ ∅ ⇒
  HD (QSORT R (SET_TO_LIST s)) ∈ s
Proof
  Cases_on`SET_TO_LIST s` \\ rw[]
  >- (Cases_on`s` \\ fs[SET_TO_LIST_THM])
  \\ Cases_on`QSORT R (SET_TO_LIST s)` \\ rfs[]
  \\ metis_tac[QSORT_PERM, MEM, MEM_PERM, MEM_SET_TO_LIST]
QED
(*--*)

Theorem image_iso[simp]:
  c1 ≅ c2 -: chu w ⇒ image c1 = image c2
Proof
  rw[image_def, EXTENSION]
  \\ `c1.world = w ∧ c2.world = w` by (
    fs[iso_objs_thm, chu_iso_bij, maps_to_in_def, chu_objects_def] \\ rfs[] )
  \\ Cases_on`x ∈ w` \\ fs[]
  \\ ntac 3 (pop_assum kall_tac)
  \\ pop_assum mp_tac
  \\ `∀c1 c2 a1 e1. c1 ≅ c2 -: chu w ∧ a1 ∈ c1.agent ∧ e1 ∈ c1.env ⇒
        ∃a2 e2. a2 ∈ c2.agent ∧ e2 ∈ c2.env ∧ c2.eval a2 e2 = c1.eval a1 e1`
     suffices_by metis_tac[iso_objs_sym, is_category_chu]
  \\ rw[iso_objs_thm, chu_iso_bij, is_chu_morphism_def]
  \\ fs[maps_to_in_def] \\ rfs[]
  \\ fs[BIJ_IFF_INV]
  \\ metis_tac[]
QED

Definition hom_comb_def:
  hom_comb m1 m2 =
        <| dom := m1.dom; cod := m2.cod; map :=
           <| map_agent := m1.map.map_agent; map_env := m2.map.map_env |> |>
End

Theorem hom_comb_id[simp]:
  hom_comb m m = m
Proof
  rw[hom_comb_def, morphism_component_equality, chu_morphism_map_component_equality]
QED

Theorem hom_comb_dom_cod[simp]:
  (hom_comb m1 m2).dom = m1.dom ∧
  (hom_comb m1 m2).cod = m2.cod
Proof
  rw[hom_comb_def]
QED

Definition homotopic_def:
  homotopic w m1 m2 ⇔
    m1 ∈ (pre_chu w).mor ∧ m2 ∈ (pre_chu w).mor ∧
    m1.dom = m2.dom ∧ m1.cod = m2.cod ∧
    hom_comb m1 m2 ∈ (pre_chu w).mor
End

(* TODO: add example of two morphisms that are not homotopic *)

Theorem homotopic_refl[simp]:
  m ∈ (pre_chu w).mor ⇒ homotopic w m m
Proof
  rw[homotopic_def] \\ metis_tac[]
QED

Theorem homotopic_sym:
  homotopic w m1 m2 ⇔ homotopic w m2 m1
Proof
  `∀m1 m2. homotopic w m1 m2 ⇒ homotopic w m2 m1` suffices_by metis_tac[]
  \\ rw[homotopic_def]
  \\ fs[hom_comb_def]
  \\ fs[pre_chu_def]
  \\ fs[is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem homotopic_trans:
  homotopic w m1 m2 ∧ homotopic w m2 m3 ⇒ homotopic w m1 m3
Proof
  rw[homotopic_def]
  \\ fs[hom_comb_def, pre_chu_def]
  \\ fs[is_chu_morphism_def]
  \\ metis_tac[]
QED

Theorem homotopic_comp:
  homotopic w ψ1 ψ2 ∧
  homotopic w φ1 φ2 ∧
  ψ1 ≈> φ1 -: chu w ∧
  ψ2 ≈> φ2 -: chu w
  ⇒
  homotopic w (φ1 o ψ1 -: chu w) (φ2 o ψ2 -: chu w)
Proof
  simp[homotopic_def]
  \\ strip_tac
  \\ simp[comp_mor_dom_cod]
  \\ rpt(conj_tac >- (imp_res_tac comp_mor_dom_cod \\ fs[]))
  \\ fs[hom_comb_def]
  \\ fs[pre_chu_def]
  \\ fs[is_chu_morphism_def]
  \\ rpt(conj_tac >- (imp_res_tac comp_mor_dom_cod \\ fs[]))
  \\ DEP_REWRITE_TAC[compose_in_thm] \\ fs[]
  \\ DEP_REWRITE_TAC[compose_thm] \\ fs[]
  \\ fs[pre_chu_def, compose_in_def, restrict_def, extensional_def, composable_in_def]
  \\ metis_tac[]
QED

Definition homotopy_equiv_def:
  homotopy_equiv w c d ⇔
    ∃f g.
      f :- c → d -: chu w ∧ g :- d → c -: chu w ∧
      homotopic w (g o f -: chu w) (id c -: chu w) ∧
      homotopic w (f o g -: chu w) (id d -: chu w)
End

val _ = overload_on("homotopy_equiv_syntax", ``λc d w. homotopy_equiv w c d``);

val _ = add_rule {
  term_name = "homotopy_equiv_syntax",
  fixity = Infix(NONASSOC,450),
  pp_elements = [HardSpace 1, TOK "\226\137\131", HardSpace 1, TM, HardSpace 1, TOK "-:"],
  paren_style = OnlyIfNecessary,
  block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))
};

Theorem homotopy_equiv_refl[simp]:
  c ∈ chu_objects w ⇒ c ≃ c -: w
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`id c -: chu w`
  \\ qexists_tac`id c -: chu w`
  \\ simp[]
  \\ match_mp_tac homotopic_refl
  \\ metis_tac[id_mor, chu_mor, is_category_chu, chu_obj]
QED

Theorem homotopy_equiv_sym:
  c ≃ d -: w ⇔ d ≃ c -: w
Proof
  rw[homotopy_equiv_def]
  \\ metis_tac[]
QED

Theorem homotopy_equiv_trans:
  c1 ≃ c2 -: w ∧ c2 ≃ c3 -: w ⇒ c1 ≃ c3 -: w
Proof
  simp[homotopy_equiv_def]
  \\ simp[GSYM AND_IMP_INTRO]
  \\ disch_then(qx_choosel_then[`f1`, `f2`]strip_assume_tac)
  \\ disch_then(qx_choosel_then[`f3`, `f4`]strip_assume_tac)
  \\ qexists_tac`f3 o f1 -: chu w`
  \\ qexists_tac`f2 o f4 -: chu w`
  \\ DEP_REWRITE_TAC[maps_to_comp]
  \\ simp[]
  \\ conj_tac >- metis_tac[]
  \\ imp_res_tac maps_to_composable
  \\ imp_res_tac composable_comp \\ fs[]
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ `homotopic w (f2 o (f4 o f3 -: chu w) -: chu w) (f2 o (id c2 -: chu w) -: chu w)`
  by (
    match_mp_tac homotopic_comp
    \\ DEP_REWRITE_TAC[homotopic_refl]
    \\ fs[composable_in_def]
    \\ fs[maps_to_in_def])
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[id_comp1] \\ fs[]
  \\ conj_asm1_tac >- fs[maps_to_in_def]
  \\ strip_tac
  \\ `homotopic w ((f2 o f4 o f3 -: chu w -: chu w) o f1 -: chu w) (f2 o f1 -: chu w)`
  by (
    match_mp_tac homotopic_comp
    \\ DEP_REWRITE_TAC[homotopic_refl]
    \\ fs[]
    \\ conj_tac >- fs[maps_to_in_def]
    \\ match_mp_tac maps_to_composable
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ qexists_tac`f2.cod`
    \\ match_mp_tac composable_maps_to \\ fs[]
    \\ simp[comp_mor_dom_cod]
    \\ fs[maps_to_in_def])
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[comp_assoc]
  \\ fs[] \\ strip_tac
  \\ conj_tac >- metis_tac[homotopic_trans]
  \\ `homotopic w (f3 o (f1 o f2 -: chu w) -: chu w) (f3 o (id c2 -: chu w) -: chu w)`
  by (
    match_mp_tac homotopic_comp
    \\ DEP_REWRITE_TAC[homotopic_refl]
    \\ fs[composable_in_def])
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[id_comp1] \\ fs[]
  \\ conj_asm1_tac >- fs[maps_to_in_def]
  \\ strip_tac
  \\ `homotopic w ((f3 o f1 o f2 -: chu w -: chu w) o f4 -: chu w) (f3 o f4 -: chu w)`
  by (
    match_mp_tac homotopic_comp
    \\ DEP_REWRITE_TAC[homotopic_refl]
    \\ fs[]
    \\ conj_tac >- fs[maps_to_in_def]
    \\ match_mp_tac maps_to_composable
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ qexists_tac`f3.cod`
    \\ match_mp_tac composable_maps_to \\ fs[]
    \\ simp[comp_mor_dom_cod])
  \\ pop_assum mp_tac
  \\ DEP_REWRITE_TAC[comp_assoc]
  \\ fs[] \\ strip_tac
  \\ metis_tac[homotopic_trans]
QED

Theorem iso_homotopy_equiv:
  c1 ≅ c2 -: chu w ⇒ c1 ≃ c2 -: w
Proof
  simp[iso_objs_thm]
  \\ simp[homotopy_equiv_def]
  \\ simp[iso_def, iso_pair_def]
  \\ strip_tac
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ qexists_tac`g`
  \\ `g ≈> f -: chu w` by (
    imp_res_tac comp_mor_dom_cod
    \\ rfs[composable_in_def] )
  \\ conj_asm1_tac
  >- ( fs[maps_to_in_def, composable_in_def] )
  \\ fs[maps_to_in_def]
  \\ DEP_REWRITE_TAC[homotopic_refl]
  \\ metis_tac[id_mor, chu_mor, is_category_chu, chu_obj, composable_obj]
QED

Definition agent_equiv_def:
  agent_equiv c a1 a2 ⇔
    (∀e. e ∈ c.env ⇒ c.eval a1 e = c.eval a2 e)
End

Definition env_equiv_def:
  env_equiv c e1 e2 ⇔
    (∀a. a ∈ c.agent ⇒ c.eval a e1 = c.eval a e2)
End

Theorem agent_equiv_equiv:
  (∀a. agent_equiv c a a) ∧
  (∀a1 a2. agent_equiv c a1 a2 ⇔ agent_equiv c a2 a1) ∧
  (∀a1 a2 a3. agent_equiv c a1 a2 ∧ agent_equiv c a2 a3 ⇒ agent_equiv c a1 a3)
Proof
  rw[agent_equiv_def] \\ metis_tac[]
QED

Theorem env_equiv_equiv:
  (∀a. env_equiv c a a) ∧
  (∀a1 a2. env_equiv c a1 a2 ⇔ env_equiv c a2 a1) ∧
  (∀a1 a2 a3. env_equiv c a1 a2 ∧ env_equiv c a2 a3 ⇒ env_equiv c a1 a3)
Proof
  rw[env_equiv_def] \\ metis_tac[]
QED

Theorem agent_env_equiv_refl[simp]:
  agent_equiv c a a ∧
  env_equiv c e e
Proof
  rw[agent_equiv_equiv, env_equiv_equiv]
QED

Theorem agent_equiv_on[simp]:
  agent_equiv c equiv_on c.agent
Proof
  rw[equiv_on_def]
  \\ metis_tac[agent_equiv_equiv]
QED

Theorem env_equiv_on[simp]:
  env_equiv c equiv_on c.env
Proof
  rw[equiv_on_def]
  \\ metis_tac[env_equiv_equiv]
QED

Definition biextensional_def:
  biextensional c ⇔
    (∀a1 a2. a1 ∈ c.agent ∧ a2 ∈ c.agent ∧ agent_equiv c a1 a2
      ⇒ a1 = a2) ∧
    (∀e1 e2. e1 ∈ c.env ∧ e2 ∈ c.env ∧ env_equiv c e1 e2
      ⇒ e1 = e2)
End

Theorem biextensional_distinct_matrix:
  FINITE c.agent ∧ FINITE c.env ⇒
    (biextensional c ⇔ ALL_DISTINCT (cf_matrix c) ∧ ALL_DISTINCT (cf_matrix (swap c)))
Proof
  rw[biextensional_def, cf_matrix_def]
  \\ qmatch_goalsub_abbrev_tac`(MAP f (QSORT R L))`
  \\ qspecl_then[`MAP f (QSORT R L)`, `MAP f L`]mp_tac ALL_DISTINCT_PERM
  \\ impl_tac >- metis_tac[QSORT_PERM, PERM_SYM, PERM_MAP]
  \\ disch_then SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`_ ∧ _ (MAP f2 (QSORT R L2))`
  \\ qspecl_then[`MAP f2 (QSORT R L2)`, `MAP f2 L2`]mp_tac ALL_DISTINCT_PERM
  \\ impl_tac >- metis_tac[QSORT_PERM, PERM_SYM, PERM_MAP]
  \\ disch_then SUBST1_TAC
  \\ simp[Abbr`f`, Abbr`f2`, Abbr`L`, Abbr`L2`]
  \\ EQ_TAC
  >- (
    strip_tac
    \\ conj_tac
    \\ irule ALL_DISTINCT_MAP_INJ
    \\ simp[MAP_EQ_f, QSORT_MEM]
    \\ ntac 2 (pop_assum mp_tac) \\ rewrite_tac[agent_equiv_def, env_equiv_def]
    \\ metis_tac[])
  \\ simp[EL_ALL_DISTINCT_EL_EQ, EL_MAP]
  \\ strip_tac
  \\ conj_tac
  >- (
    rw[agent_equiv_def]
    \\ `MEM a1 (SET_TO_LIST c.agent) ∧ MEM a2 (SET_TO_LIST c.agent)` by fs[]
    \\ fs[MEM_EL]
    \\ first_x_assum(first_assum o mp_then Any mp_tac)
    \\ disch_then(last_assum o mp_then Any mp_tac)
    \\ simp[MAP_EQ_f, QSORT_MEM]
    \\ metis_tac[])
  \\ rw[env_equiv_def]
  \\ `MEM e1 (SET_TO_LIST c.env) ∧ MEM e2 (SET_TO_LIST c.env)` by fs[]
  \\ fs[MEM_EL]
  \\ last_x_assum(first_assum o mp_then Any mp_tac)
  \\ disch_then(last_assum o mp_then Any mp_tac)
  \\ simp[MAP_EQ_f, QSORT_MEM]
  \\ metis_tac[]
QED

Theorem biextensional_swap[simp]:
  biextensional (swap c) ⇔ biextensional c
Proof
  rw[biextensional_def]
  \\ rw[agent_equiv_def, env_equiv_def]
  \\ metis_tac[]
QED

Theorem biextensional_homotopy_equiv_iso:
  biextensional c ∧ biextensional d ⇒
    (c ≃ d -: w ⇔ c ≅ d -: chu w)
Proof
  strip_tac
  \\ reverse eq_tac
  >- metis_tac[iso_homotopy_equiv]
  \\ simp[homotopy_equiv_def]
  \\ strip_tac
  \\ simp[iso_objs_thm]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ simp[chu_iso_bij]
  \\ rewrite_tac[Once CONJ_ASSOC]
  \\ reverse conj_asm2_tac
  >- ( imp_res_tac maps_to_composable
       \\ fs[composable_in_def, pre_chu_def] )
  \\ imp_res_tac homotopic_sym
  \\ fs[homotopic_def, pre_chu_def]
  \\ imp_res_tac maps_to_obj \\ fs[]
  \\ rpt(qpat_x_assum`T`kall_tac)
  \\ rpt(qpat_x_assum`is_chu_morphism _ _ (hom_comb _ _).map`mp_tac)
  \\ simp[hom_comb_def, chu_id_morphism_map_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ conj_asm1_tac >- ( imp_res_tac maps_to_composable \\ fs[] )
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ conj_asm1_tac >- fs[composable_in_def]
  \\ simp[pre_chu_def]
  \\ `f.dom = c ∧ g.dom = d ∧ f.cod = d ∧ g.cod = c` by fs[maps_to_in_def]
  \\ rpt (BasicProvers.VAR_EQ_TAC)
  \\ ntac 2(qpat_x_assum`_ = (_ _ _).cod`(assume_tac o SYM))
  \\ ntac 2(qpat_x_assum`_ = (_ _ _).dom`(assume_tac o SYM))
  \\ rfs[]
  \\ simp[is_chu_morphism_def]
  \\ ntac 4 strip_tac
  \\ fs[restrict_def]
  \\ ntac 2 (qpat_x_assum`biextensional _`mp_tac)
  \\ fs[is_chu_morphism_def]
  \\ simp[biextensional_def]
  \\ ntac 2 strip_tac
  \\ simp[BIJ_IFF_INV]
  \\ conj_tac
  >- (
    qexists_tac`g.map.map_agent`
    \\ imp_res_tac maps_to_in_def
    \\ fs[pre_chu_def, is_chu_morphism_def]
    \\ PROVE_TAC[agent_equiv_def])
  \\ qexists_tac`g.map.map_env`
  \\ imp_res_tac maps_to_in_def
  \\ fs[pre_chu_def, is_chu_morphism_def]
  \\ rw[]
  \\ first_x_assum (fn th =>
       match_mp_tac th
       \\ rw[]
       \\ rw[env_equiv_def]
       \\ NO_TAC)
QED

Definition min_elt_def:
  min_elt R s = @x. x ∈ s ∧ ∀y. y ∈ s ⇒R x y
End

val _ = temp_overload_on("rep", ``min_elt (RC (SHORTLEX char_lt))``)

Definition biextensional_collapse_def:
  biextensional_collapse c = mk_cf
    <| world := c.world;
       agent := IMAGE (min_elt (RC (SHORTLEX char_lt)) o (equiv_class (agent_equiv c) c.agent)) c.agent;
       env := IMAGE (min_elt (RC (SHORTLEX char_lt)) o (equiv_class (env_equiv c) c.env)) c.env;
       eval := c.eval |>
End

val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^"],
                   term_name = "biextensional_collapse" }

Theorem rep_in:
  s ≠ ∅ ⇒ rep s ∈ s
Proof
  rw[min_elt_def]
  \\ SELECT_ELIM_TAC
  \\ simp[]
  \\ mp_tac (MATCH_MP WF_SHORTLEX WF_char_lt)
  \\ rewrite_tac[WF_DEF]
  \\ disch_then(qspec_then`s`mp_tac)
  \\ impl_tac >- metis_tac[IN_DEF, MEMBER_NOT_EMPTY]
  \\ strip_tac
  \\ qexists_tac`min`
  \\ `total (RC char_lt)`
  by ( simp[RC_char_lt] \\ simp[total_def, char_le_def] )
  \\ imp_res_tac SHORTLEX_total
  \\ fs[IN_DEF, RC_DEF, total_def]
  \\ metis_tac[]
QED

Theorem rep_in_equiv_class[simp]:
  R equiv_on s ∧ x ∈ s ⇒
  rep (equiv_class R s x) ∈ s ∧
  rep (equiv_class R s x) ∈ equiv_class R s x
Proof
  strip_tac
  \\ `x ∈ equiv_class R s x` by ( simp[equiv_class_element] \\ fs[equiv_on_def] )
  \\ imp_res_tac MEMBER_NOT_EMPTY
  \\ imp_res_tac rep_in
  \\ fs[]
QED

Theorem eval_equiv:
  a ∈ c.agent ∧ e ∈ c.env ∧
  a' ∈ equiv_class (agent_equiv c) c.agent a ∧
  e' ∈ equiv_class (env_equiv c) c.env e ⇒
  c.eval a' e' = c.eval a e
Proof
  rw[agent_equiv_def, env_equiv_def]
QED

Theorem image_biextensional_collapse[simp]:
  image (biextensional_collapse c) = image c
Proof
  rw[biextensional_collapse_def, image_def, EXTENSION, mk_cf_def]
  \\ metis_tac[eval_equiv, rep_in_equiv_class, MEMBER_NOT_EMPTY, agent_equiv_on, env_equiv_on]
QED

Theorem biextensional_collapse_biextensional:
  biextensional (biextensional_collapse c)
Proof
  rw[biextensional_def]
  \\ fs[biextensional_collapse_def, mk_cf_def, PULL_EXISTS] \\ rw[]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[equiv_class_eq]
  \\ simp[]
  >- (
    qmatch_rename_tac`agent_equiv c a1 a2`
    \\ pop_assum mp_tac \\ simp[Once agent_equiv_def, PULL_EXISTS] \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`c.eval x1 _`
    \\ qmatch_asmsub_abbrev_tac`x1 = min_elt _ s1`
    \\ qmatch_asmsub_abbrev_tac`_ = COND _ (c.eval x2 _) _`
    \\ qmatch_asmsub_abbrev_tac`x2 = min_elt _ s2`
    \\ `a1 ∈ s1` by simp[Abbr`s1`, agent_equiv_equiv]
    \\ `a2 ∈ s2` by simp[Abbr`s2`, agent_equiv_equiv]
    \\ `x1 ∈ s1` by (simp[Abbr`x1`] \\ metis_tac[MEMBER_NOT_EMPTY,rep_in])
    \\ `x2 ∈ s2` by (simp[Abbr`x2`] \\ metis_tac[MEMBER_NOT_EMPTY,rep_in])
    \\ `agent_equiv c x1 a1`
    by (
      rw[agent_equiv_def]
      \\ match_mp_tac eval_equiv
      \\ qunabbrev_tac`x1`
      \\ qunabbrev_tac`s1`
      \\ DEP_REWRITE_TAC[rep_in]
      \\ simp[env_equiv_equiv]
      \\ simp[EXTENSION]
      \\ metis_tac[agent_equiv_equiv] )
    \\ `agent_equiv c x1 x2`
    by (
      simp[agent_equiv_def] \\ rw[]
      \\ first_x_assum(qspec_then`e`mp_tac)
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ ntac 2 (pop_assum kall_tac)
      \\ rw[]
      \\ qmatch_asmsub_abbrev_tac`c.eval x1 (min_elt _ t1)`
      \\ qmatch_asmsub_abbrev_tac`c.eval x1 y1`
      \\ `e ∈ t1` by simp[Abbr`t1`, env_equiv_equiv]
      \\ `y1 ∈ t1` by (simp[Abbr`y1`] \\ metis_tac[MEMBER_NOT_EMPTY,rep_in])
      \\ `c.eval x1 e = c.eval x1 y1`
      by ( fs[Abbr`t1`, env_equiv_def, Abbr`s1`] )
      \\ `c.eval x2 e = c.eval x2 y1`
      by ( fs[Abbr`t1`, env_equiv_def, Abbr`s2`] )
      \\ fs[] )
    \\ `agent_equiv c x2 a2`
    by (
      rw[agent_equiv_def]
      \\ match_mp_tac eval_equiv
      \\ qunabbrev_tac`x2`
      \\ qunabbrev_tac`s2`
      \\ DEP_REWRITE_TAC[rep_in]
      \\ simp[env_equiv_equiv]
      \\ simp[EXTENSION]
      \\ metis_tac[agent_equiv_equiv] )
    \\ metis_tac[agent_equiv_equiv])
  \\ qmatch_rename_tac`env_equiv c a1 a2`
  \\ pop_assum mp_tac \\ simp[Once env_equiv_def, PULL_EXISTS] \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`c.eval _ x1`
  \\ qmatch_asmsub_abbrev_tac`x1 = min_elt _ s1`
  \\ qmatch_asmsub_abbrev_tac`_ = COND _ (c.eval _ x2) _`
  \\ qmatch_asmsub_abbrev_tac`x2 = min_elt _ s2`
  \\ `a1 ∈ s1` by simp[Abbr`s1`, env_equiv_equiv]
  \\ `a2 ∈ s2` by simp[Abbr`s2`, env_equiv_equiv]
  \\ `x1 ∈ s1` by (simp[Abbr`x1`] \\ metis_tac[MEMBER_NOT_EMPTY,rep_in])
  \\ `x2 ∈ s2` by (simp[Abbr`x2`] \\ metis_tac[MEMBER_NOT_EMPTY,rep_in])
  \\ `env_equiv c x1 a1`
  by (
    rw[env_equiv_def]
    \\ match_mp_tac eval_equiv
    \\ qunabbrev_tac`x1`
    \\ qunabbrev_tac`s1`
    \\ DEP_REWRITE_TAC[rep_in]
    \\ simp[agent_equiv_equiv]
    \\ simp[EXTENSION]
    \\ metis_tac[env_equiv_equiv] )
  \\ `env_equiv c x1 x2`
  by (
    simp[env_equiv_def] \\ rw[]
    \\ first_x_assum(qspec_then`a`mp_tac)
    \\ simp[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ ntac 2 (pop_assum kall_tac)
    \\ rw[]
    \\ qmatch_asmsub_abbrev_tac`c.eval (min_elt _ t1) x1`
    \\ qmatch_asmsub_abbrev_tac`c.eval y1 x1`
    \\ `a ∈ t1` by simp[Abbr`t1`, agent_equiv_equiv]
    \\ `y1 ∈ t1` by (simp[Abbr`y1`] \\ metis_tac[MEMBER_NOT_EMPTY,rep_in])
    \\ `c.eval a x1 = c.eval y1 x1`
    by ( fs[Abbr`t1`, agent_equiv_def, Abbr`s1`] )
    \\ `c.eval a x2 = c.eval y1 x2`
    by ( fs[Abbr`t1`, agent_equiv_def, Abbr`s2`] )
    \\ fs[] )
  \\ `env_equiv c x2 a2`
  by (
    rw[env_equiv_def]
    \\ match_mp_tac eval_equiv
    \\ qunabbrev_tac`x2`
    \\ qunabbrev_tac`s2`
    \\ DEP_REWRITE_TAC[rep_in]
    \\ simp[agent_equiv_equiv]
    \\ simp[EXTENSION]
    \\ metis_tac[env_equiv_equiv] )
  \\ metis_tac[env_equiv_equiv]
QED

Theorem biextensional_iso:
  biextensional c ∧ c ≅ d -: chu w ⇒ biextensional d
Proof
  rw[iso_objs_thm, chu_iso_bij]
  \\ fs[maps_to_in_def]
  \\ fs[pre_chu_def]
  \\ fs[is_chu_morphism_def]
  \\ fs[BIJ_IFF_INV]
  \\ qpat_x_assum`biextensional _`mp_tac
  \\ simp[biextensional_def]
  \\ rewrite_tac[agent_equiv_def, env_equiv_def]
  \\ metis_tac[]
QED

Theorem biextensional_collapse_in_chu_objects[simp]:
  c ∈ chu_objects w ⇒ biextensional_collapse c ∈ chu_objects w
Proof
  rw[chu_objects_def, biextensional_collapse_def, image_def, SUBSET_DEF]
  \\ fs[wf_def]
QED

Theorem equiv_class_rep_eq:
  R equiv_on s ∧ x ∈ s⇒
  (equiv_class R s (rep (equiv_class R s x))) = (equiv_class R s x)
Proof
  strip_tac
  \\ `x ∈ equiv_class R s x` by ( simp[equiv_class_element] \\ fs[equiv_on_def] )
  \\ imp_res_tac MEMBER_NOT_EMPTY
  \\ imp_res_tac rep_in
  \\ DEP_REWRITE_TAC[equiv_class_eq]
  \\ fs[]
  \\ fs[equiv_on_def]
QED

Theorem min_elt_sing[simp]:
  R x x ⇒ min_elt R {x} = x
Proof
  rw[min_elt_def] \\ metis_tac[]
QED

Theorem biextensional_iff_iso_collapse:
  c ∈ chu_objects w ⇒
  (biextensional c ⇔ c ≅ (biextensional_collapse c) -: chu w)
Proof
  strip_tac
  \\ reverse EQ_TAC
  >- metis_tac[biextensional_iso, biextensional_collapse_biextensional,
               iso_objs_sym, is_category_chu]
  \\ simp[iso_objs_thm]
  \\ rewrite_tac[biextensional_def]
  \\ rewrite_tac[GSYM agent_equiv_def, GSYM env_equiv_def]
  \\ strip_tac
  \\ qexists_tac`mk_chu_morphism c (biextensional_collapse c)
                   <| map_agent := min_elt (RC (SHORTLEX char_lt)) o
                                     equiv_class (agent_equiv c) c.agent;
                      map_env := min_elt (RC (SHORTLEX char_lt)) o
                                     equiv_class (env_equiv c) c.env |>`
  \\ qmatch_goalsub_abbrev_tac`mk_chu_morphism _ _ f`
  \\ conj_asm1_tac
  >- (
    simp[mk_chu_morphism_def, maps_to_in_def, pre_chu_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[biextensional_collapse_def, PULL_EXISTS]
    \\ simp[restrict_def, mk_cf_def]
    \\ conj_tac >- ( reverse(rw[]) >- metis_tac[] \\ simp[Abbr`f`] )
    \\ conj_tac >- ( rw[Abbr`f`] \\ metis_tac[] )
    \\ rpt gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ simp[Abbr`f`]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ DEP_REWRITE_TAC[equiv_class_rep_eq]
    \\ simp[]
    \\ qmatch_abbrev_tac`_ = c.eval a' _`
    \\ `a' ∈ equiv_class (agent_equiv c) c.agent a` by ( simp[Abbr`a'`] )
    \\ pop_assum mp_tac
    \\ rewrite_tac[agent_equiv_def]
    \\ simp_tac (srw_ss())[] \\ rw[])
  \\ simp[chu_iso_bij]
  \\ fs[maps_to_in_def, pre_chu_def]
  \\ fs[mk_chu_morphism_def]
  \\ simp[BIJ_restrict]
  \\ pop_assum kall_tac
  \\ `∀x. x ∈ c.agent ⇒ equiv_class (agent_equiv c) c.agent x = {x}`
  by ( rw[EXTENSION] \\ metis_tac[agent_equiv_def] )
  \\ `∀x. x ∈ c.env ⇒ equiv_class (env_equiv c) c.env x = {x}`
  by ( rw[EXTENSION] \\ metis_tac[env_equiv_def] )
  \\ simp[BIJ_IFF_INV]
  \\ simp[Abbr`f`, biextensional_collapse_def, PULL_EXISTS]
  \\ qexists_tac`I` \\ qexists_tac`I`
  \\ rw[]
  \\ qexists_tac`x` \\ rw[]
QED

Theorem homotopy_equiv_collapse:
  c ∈ chu_objects w ⇒ c ≃ c ^ -: w
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism c c^ <| map_agent := rep o equiv_class (agent_equiv c) c.agent;
                                         map_env := I |>`
  \\ qmatch_goalsub_abbrev_tac`mk_chu_morphism _ _ f`
  \\ qexists_tac`mk_chu_morphism c^ c <| map_agent := I;
                                         map_env := rep o equiv_class (env_equiv c) c.env |>`
  \\ simp[Once CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    simp[mk_chu_morphism_def]
    \\ simp[maps_to_in_def]
    \\ simp[pre_chu_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[biextensional_collapse_def, PULL_EXISTS, restrict_def, mk_cf_def]
    \\ rw[Abbr`f`]
    \\ metis_tac[rep_in_equiv_class, equiv_class_element, agent_equiv_def,
                 agent_equiv_on, env_equiv_on, env_equiv_def] )
  \\ qunabbrev_tac`f`
  \\ qmatch_asmsub_abbrev_tac`f :- c → c^ -: _`
  \\ qmatch_asmsub_abbrev_tac`g :- c^ → c -: _`
  \\ fs[]
  \\ imp_res_tac maps_to_comp \\ fs[]
  \\ imp_res_tac maps_to_in_def
  \\ imp_res_tac maps_to_obj
  \\ conj_tac
  \\ fs[homotopic_def]
  \\ (conj_tac >- metis_tac[id_mor, chu_mor, chu_obj, is_category_chu])
  \\ simp[hom_comb_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ imp_res_tac maps_to_composable
  \\ simp[pre_chu_def]
  \\ simp[is_chu_morphism_def, chu_id_morphism_map_def]
  \\ simp[restrict_def]
  \\ simp[Abbr`f`, Abbr`g`, mk_chu_morphism_def, restrict_def]
  \\ simp[biextensional_collapse_def, PULL_EXISTS, mk_cf_def]
  \\ rw[]
  \\ simp[equiv_class_rep_eq]
  \\ metis_tac[rep_in_equiv_class, equiv_class_element, agent_equiv_def,
               agent_equiv_on, env_equiv_on, env_equiv_def]
QED

Theorem homotopy_equiv_iff_iso_collapse:
  c ∈ chu_objects w ∧ d ∈ chu_objects w ⇒
  (c ≃ d -: w ⇔ c^ ≅ d^ -: chu w)
Proof
  metis_tac[biextensional_homotopy_equiv_iso, biextensional_collapse_biextensional,
            homotopy_equiv_trans, homotopy_equiv_sym, homotopy_equiv_collapse]
QED

Theorem homotopy_equiv_class_unique_biextensional:
  c ∈ chu_objects w ⇒
  ∀x. biextensional x ∧ x ∈ equiv_class (homotopy_equiv w) (chu_objects w) c ⇔ x ≅ c ^ -: chu w
Proof
  rw[EQ_IMP_THM]
  \\ imp_res_tac iso_objs_objs \\ fs[]
  \\ metis_tac[biextensional_iff_iso_collapse, biextensional_collapse_biextensional,
               iso_objs_sym, is_category_chu, biextensional_iso, iso_objs_trans,
               homotopy_equiv_collapse, homotopy_equiv_trans, homotopy_equiv_sym,
               homotopy_equiv_iff_iso_collapse]
QED

(* TODO: example of homotopy equivalent cfs proved via isomorphic collapse *)

Theorem agent_env_equiv_swap[simp]:
  agent_equiv (swap c) = env_equiv c ∧
  env_equiv (swap c) = agent_equiv c
Proof
  rw[FUN_EQ_THM, agent_equiv_def, env_equiv_def]
QED

Theorem biextensional_collapse_swap:
  biextensional_collapse (swap c) = swap (biextensional_collapse c)
Proof
  rw[cf_component_equality, biextensional_collapse_def, swap_def, mk_cf_def]
  \\ rw[FUN_EQ_THM] \\ rw[] \\ fs[] \\ metis_tac[]
QED

Theorem homotopy_equiv_swap[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ⇒
  (swap c1 ≃ swap c2 -: w ⇔ c1 ≃ c2 -: w)
Proof
  `∀c1 c2. c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ c1 ≃ c2 -: w ⇒ swap c1 ≃ swap c2 -: w`
  suffices_by metis_tac[swap_swap, swap_in_chu_objects]
  \\ rw[]
  \\ `c1^ ≅ c2^ -: chu w` by simp[GSYM homotopy_equiv_iff_iso_collapse]
  \\ simp[homotopy_equiv_iff_iso_collapse]
  \\ simp[biextensional_collapse_swap]
QED

Theorem homotopy_equiv_image[simp]:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧
  c1 ≃ c2 -: w ⇒ image c1 = image c2
Proof
  rw[]
  \\ rfs[homotopy_equiv_iff_iso_collapse]
  \\ imp_res_tac image_iso \\ fs[]
QED

Theorem homotopy_equiv_sum_right:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧ d ∈ chu_objects w ∧
  c1 ≃ c2 -: w ⇒
  sum c1 d ≃ sum c2 d -: w
Proof
  rw[homotopy_equiv_def]
  \\ qexists_tac`mk_chu_morphism (sum c1 d) (sum c2 d)
        <| map_agent := λa. encode_sum (sum_CASE (decode_sum a) (INL o f.map.map_agent) (INR o I));
           map_env := λe. encode_pair (f.map.map_env (FST (decode_pair e)), SND (decode_pair e)) |>`
  \\ qmatch_goalsub_abbrev_tac`m :- _ → _ -: _`
  \\ pop_assum mp_tac
  \\ qho_match_abbrev_tac`Abbrev (m = G c1 c2 d f) ⇒ _`
  \\ strip_tac
  \\ qexists_tac`G c2 c1 d g`
  \\ qunabbrev_tac`m`
  \\ qho_match_abbrev_tac`P1 c1 c2 f ∧ P1 c2 c1 g ∧ P2 c1 c2 f g ∧ P2 c2 c1 g f`
  \\ rpt(first_x_assum(fn th =>
        if List.null(Lib.intersect(map (#1 o dest_var) (free_vars (concl th)))["c1","c2","f","g"])
        then NO_TAC
        else mp_tac th))
  \\ rewrite_tac[AND_IMP_INTRO]
  \\ qho_match_abbrev_tac`H c1 c2 f g ⇒ _`
  \\ `∀c1 c2 f g. H c1 c2 f g ⇒ P1 c1 c2 f ∧ P2 c1 c2 f g` suffices_by metis_tac[]
  \\ simp[Abbr`H`, GSYM CONJ_ASSOC]
  \\ rpt gen_tac \\ strip_tac
  \\ simp[Abbr`P1`]
  \\ conj_asm1_tac
  >- (
    qpat_x_assum`f :- _ → _ -: _`mp_tac
    \\ simp[maps_to_in_def, pre_chu_def]
    \\ simp[Abbr`G`, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[sum_def, PULL_EXISTS, restrict_def, EXISTS_PROD]
    \\ strip_tac \\ fs[]
    \\ rw[] \\ rw[] \\ rw[sum_eval_def, mk_cf_def] )
  \\ `G c2 c1 d g :- sum c2 d → sum c1 d -: chu w`
  by (
    qpat_x_assum`g :- _ → _ -: _`mp_tac
    \\ simp[maps_to_in_def, pre_chu_def]
    \\ simp[Abbr`G`, mk_chu_morphism_def]
    \\ simp[is_chu_morphism_def]
    \\ simp[sum_def, PULL_EXISTS, restrict_def, EXISTS_PROD]
    \\ strip_tac \\ fs[]
    \\ rw[] \\ rw[] \\ rw[sum_eval_def, mk_cf_def] )
  \\ simp[Abbr`P2`]
  \\ qpat_x_assum`homotopic _ _ (id c1 -: _)`mp_tac
  \\ `g o f -: chu w :- c1 → c1 -: chu w` by metis_tac[maps_to_comp, is_category_chu]
  \\ `G c2 c1 d g o G c1 c2 d f -: chu w :- sum c1 d → sum c1 d -: chu w`
    by metis_tac[maps_to_comp, is_category_chu]
  \\ simp[homotopic_def]
  \\ imp_res_tac maps_to_in_def \\ fs[]
  \\ strip_tac
  \\ conj_tac >- metis_tac[id_mor, maps_to_obj, is_category_chu, chu_obj, chu_mor]
  \\ pop_assum mp_tac
  \\ simp[pre_chu_def]
  \\ simp[is_chu_morphism_def]
  \\ simp[hom_comb_def]
  \\ simp[chu_id_morphism_map_def, restrict_def]
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ simp[]
  \\ conj_asm1_tac >- (imp_res_tac maps_to_composable \\ fs[])
  \\ DEP_REWRITE_TAC[chu_comp] \\ simp[]
  \\ simp[Abbr`G`, pre_chu_def, restrict_def, extensional_def, sum_def, PULL_EXISTS, EXISTS_PROD]
  \\ rw[mk_chu_morphism_def, restrict_def] \\ rw[] \\ rw[] \\ fs[pre_chu_def, is_chu_morphism_def]
  \\ rw[sum_eval_def, mk_cf_def]
  \\ metis_tac[]
QED

Theorem homotopy_equiv_sum:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧
  d1 ∈ chu_objects w ∧ d2 ∈ chu_objects w ∧
  c1 ≃ c2 -: w ∧ d1 ≃ d2 -: w ⇒
  sum c1 d1 ≃ sum c2 d2 -: w
Proof
  metis_tac[homotopy_equiv_refl, homotopy_equiv_trans, sum_comm,
            iso_homotopy_equiv, homotopy_equiv_sum_right]
QED

Theorem homotopy_equiv_prod:
  c1 ∈ chu_objects w ∧ c2 ∈ chu_objects w ∧
  d1 ∈ chu_objects w ∧ d2 ∈ chu_objects w ∧
  c1 ≃ c2 -: w ∧ d1 ≃ d2 -: w ⇒
  prod c1 d1 ≃ prod c2 d2 -: w
Proof
  strip_tac
  \\ rewrite_tac[GSYM swap_sum_prod]
  \\ DEP_REWRITE_TAC[homotopy_equiv_swap]
  \\ DEP_REWRITE_TAC[homotopy_equiv_sum]
  \\ DEP_REWRITE_TAC[homotopy_equiv_swap]
  \\ simp[]
QED

Definition null_def:
  null w = <| world := w; agent := ∅; env := ∅; eval := K (K ARB)|>
End

Theorem null_prod_null[simp]:
  null w && null w = null w
Proof
  rw[null_def, prod_def, mk_cf_def, FUN_EQ_THM]
QED

Theorem wf_null[simp]:
  wf (null w)
Proof
  rw[wf_def, null_def]
QED

Theorem null_in_chu_objects[simp]:
  null w ∈ chu_objects w
Proof
  rw[chu_objects_def] \\ rw[null_def]
QED

Theorem biextensional_collapse_idem[simp]:
  wf c ∧ biextensional c ⇒ biextensional_collapse c = c
Proof
  simp[cf_component_equality, biextensional_collapse_def, mk_cf_def]
  \\ strip_tac
  \\ `∀x. x ∈ c.agent ⇒ equiv_class (agent_equiv c) c.agent x = {x}`
  by ( rw[EXTENSION] \\ fs[biextensional_def] \\ fs[agent_equiv_def] \\ metis_tac[] )
  \\ `∀x. x ∈ c.env ⇒ equiv_class (env_equiv c) c.env x = {x}`
  by ( rw[EXTENSION] \\ fs[biextensional_def] \\ fs[env_equiv_def] \\ metis_tac[] )
  \\ simp[EXTENSION, PULL_EXISTS, PULL_FORALL]
  \\ qx_gen_tac`a`
  \\ qx_gen_tac`e`
  \\ rw[EQ_IMP_THM, FUN_EQ_THM] \\ rw[]
  \\ TRY (qexists_tac`a` \\ simp[] \\ NO_TAC)
  \\ TRY (qexists_tac`e` \\ simp[] \\ NO_TAC)
  \\ fs[wf_def]
  \\ first_x_assum match_mp_tac
  \\ metis_tac[rep_in_equiv_class, agent_equiv_on, env_equiv_on, IN_SING]
QED

Theorem biextensional_cf0[simp]:
  biextensional (cf0 w)
Proof
  rw[biextensional_def, cf0_def]
QED

Theorem biextensional_swap[simp]:
  biextensional (swap c) ⇔ biextensional c
Proof
  rw[biextensional_def]
  \\ metis_tac[]
QED

Theorem biextensional_cfT[simp]:
  biextensional (cfT w)
Proof
  rw[cfT_def]
QED

Theorem empty_agent_nonempty_env:
  c ∈ chu_objects w ∧
  c.agent = ∅ ∧ c.env ≠ ∅ ⇒ c ≃ cf0 w -: w
Proof
  rw[]
  \\ rw[homotopy_equiv_iff_iso_collapse]
  \\ rw[iso_objs_thm]
  \\ rw[chu_iso_bij]
  \\ `∀x. x ∈ c.env ⇒ equiv_class (env_equiv c) c.env x = c.env`
  by ( rw[EXTENSION, env_equiv_def] )
  \\ `CHOICE c.env ∈ c.env` by metis_tac[CHOICE_DEF]
  \\ qexists_tac`mk_chu_morphism (biextensional_collapse c) (cf0 w)
                   <| map_agent := ARB; map_env := K (rep c.env) |>`
  \\ rw[maps_to_in_def, pre_chu_def, mk_chu_morphism_def, restrict_def,
        is_chu_morphism_def, extensional_def]
  \\ fs[cf0_def, biextensional_collapse_def] \\ rfs[]
  \\ rw[BIJ_IFF_INV, PULL_EXISTS, PULL_FORALL]
  \\ TRY(qexists_tac`K ""` \\ rw[])
  \\ metis_tac[CHOICE_DEF]
QED

Theorem empty_env_nonempty_agent:
  c ∈ chu_objects w ∧ c.env = ∅ ∧ c.agent  ≠ ∅ ⇒ c ≃ cfT w -: w
Proof
  rw[]
  \\ rw[homotopy_equiv_iff_iso_collapse]
  \\ rw[iso_objs_thm]
  \\ rw[chu_iso_bij]
  \\ `∀x. x ∈ c.agent ⇒ equiv_class (agent_equiv c) c.agent x = c.agent`
  by ( rw[EXTENSION, agent_equiv_def] )
  \\ qexists_tac`mk_chu_morphism (biextensional_collapse c) (cfT w)
                   <| map_env := ARB; map_agent := K "" |>`
  \\ rw[maps_to_in_def, pre_chu_def, mk_chu_morphism_def, restrict_def,
        is_chu_morphism_def, extensional_def]
  \\ fs[cfT_agent_env, biextensional_collapse_def] \\ rfs[cf_component_equality, cfT_agent_env]
  >- (
    rw[mk_cf_def, cfT_def, swap_def, cf0_def, FUN_EQ_THM]
    \\ qmatch_abbrev_tac`rep s = ""`
    \\ `s = {""}` suffices_by rw[]
    \\ simp[Abbr`s`, EXTENSION, agent_equiv_def] )
  \\ rw[BIJ_IFF_INV]
  \\ qexists_tac`K (rep c.agent)` \\ rw[]
  \\ metis_tac[CHOICE_DEF]
QED

Theorem empty_image:
  c ∈ chu_objects w ∧ biextensional c ∧ image c = ∅ ⇒
  c ≅ cf0 w -: chu w ∨ c ≅ cfT w -: chu w ∨ c = null w
Proof
  rw[]
  \\ Cases_on`c.env ≠ ∅ ∧ c.agent ≠ ∅`
  >- (
    `F` suffices_by rw[]
    \\ qpat_x_assum`image _ = _`mp_tac
    \\ fs[GSYM MEMBER_NOT_EMPTY]
    \\ simp[image_def]
    \\ metis_tac[] )
  \\ Cases_on`c.env = ∅ ∧ c.agent = ∅`
  >- (
    rpt disj2_tac
    \\ rw[cf_component_equality, null_def]
    \\ fs[chu_objects_def, wf_def]
    \\ simp[FUN_EQ_THM] )
  \\ metis_tac[biextensional_homotopy_equiv_iso,
               biextensional_cfT, biextensional_cf0,
               empty_agent_nonempty_env, empty_env_nonempty_agent]
QED

Definition cf1_def:
  cf1 w s = mk_cf <| world := w; agent := {""}; env := s; eval := λa e. e |>
End

Definition cfbot_def:
  cfbot w s = swap (cf1 w s)
End

Theorem cf1_components[simp]:
  (cf1 w s).world = w ∧
  (cf1 w s).agent = {""} ∧
  (cf1 w s).env = s
Proof
  rw[cf1_def]
QED

Theorem cf1_empty:
  cf1 w ∅ = cfT w
Proof
  rw[cf1_def, cf_component_equality, cfT_agent_env]
  \\ rw[cfT_def, cf0_def, mk_cf_def, swap_def, FUN_EQ_THM]
QED

Theorem cfbot_empty:
  cfbot w ∅ = cf0 w
Proof
  rw[cfbot_def, cf_component_equality, cf1_def, cf0_def]
  \\ EVAL_TAC \\ simp[FUN_EQ_THM]
QED

Theorem biextensional_cf1[simp]:
  biextensional (cf1 w s)
Proof
  rw[biextensional_def, cf1_def, mk_cf_def] \\ rfs[env_equiv_def]
QED

Theorem biextensional_cfbot[simp]:
  biextensional (cfbot w s)
Proof
  rw[cfbot_def]
QED

Theorem wf_cf1[simp]:
  s ⊆ w ⇒ wf (cf1 w s)
Proof
  rw[cf1_def, image_def]
QED

Theorem wf_cfbot[simp]:
  s ⊆ w ⇒ wf (cfbot w s)
Proof
  rw[cfbot_def]
QED

Theorem cf1_in_chu_objects[simp]:
  s ⊆ w ⇒ cf1 w s ∈ chu_objects w
Proof
  rw[chu_objects_def] \\ rw[cf1_def]
QED

Theorem cfbot_in_chu_objects[simp]:
  s ⊆ w ⇒ cfbot w s ∈ chu_objects w
Proof
  rw[cfbot_def]
QED

Theorem sing_agent:
  c ∈ chu_objects w ∧ SING (c.agent) ⇒ c ≃ cf1 w (image c) -: w
Proof
  rw[SING_DEF]
  \\ `image c ⊆ w` by (
    fs[chu_objects_def, wf_def, image_def, SUBSET_DEF, PULL_EXISTS] \\ rw[] )
  \\ `c ^ ≅ cf1 w (image c) -: chu w` suffices_by
     metis_tac[homotopy_equiv_iff_iso_collapse,
               cf1_in_chu_objects, homotopy_equiv_sym,
               biextensional_collapse_idem, wf_cf1,
               biextensional_cf1]
  \\ rw[iso_objs_thm, chu_iso_bij]
  \\ qexists_tac`mk_chu_morphism (biextensional_collapse c) (cf1 w (image c))
       <| map_agent := K ""; map_env := λs. rep { e | e ∈ c.env ∧ c.eval x e = s } |>`
  \\ simp[mk_chu_morphism_def]
  \\ conj_asm1_tac
  >- (
    simp[maps_to_in_def, pre_chu_def]
    \\ simp[is_chu_morphism_def, restrict_def, extensional_def]
    \\ simp[cf1_def, mk_cf_def]
    \\ simp[biextensional_collapse_def, mk_cf_def]
    \\ simp[image_def, PULL_EXISTS]
    \\ simp[env_equiv_def]
    \\ rw[]
    \\ TRY (
      TRY (`F` suffices_by rw[] \\ qpat_x_assum`¬_`mp_tac \\ simp[])
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ AP_TERM_TAC \\ rw[EXTENSION] \\ metis_tac[] )
    \\ qmatch_abbrev_tac`c.eval x1 y1 = _`
    \\ `x1 = rep {x}`
    by (
      qunabbrev_tac`x1`
      \\ AP_TERM_TAC
      \\ simp[EXTENSION, agent_equiv_def]
      \\ metis_tac[] )
    \\ qmatch_asmsub_abbrev_tac`y1 = rep s`
    \\ `y1 ∈ s` by (
      qunabbrev_tac`y1`
      \\ match_mp_tac rep_in
      \\ simp[Abbr`s`,GSYM MEMBER_NOT_EMPTY]
      \\ metis_tac[] )
    \\ pop_assum mp_tac
    \\ simp[Abbr`s`] )
  \\ qmatch_goalsub_abbrev_tac`is_chu_morphism _ _ f`
  \\ imp_res_tac maps_to_in_def
  \\ fs[pre_chu_def]
  \\ conj_tac
  >- (
    simp[BIJ_IFF_INV, restrict_def]
    \\ simp[biextensional_collapse_def]
    \\ qmatch_goalsub_abbrev_tac`_ "" = xx`
    \\ qexists_tac`K xx` \\ rw[] )
  \\ simp[BIJ_IFF_INV, restrict_def]
  \\ simp[biextensional_collapse_def, PULL_EXISTS]
  \\ simp[image_def, PULL_EXISTS]
  \\ simp[env_equiv_def]
  \\ qexists_tac`c.eval x`
  \\ rw[]
  \\ (qmatch_goalsub_abbrev_tac`_ = (rep s)` ORELSE qmatch_goalsub_abbrev_tac`rep s`)
  \\ `rep s ∈ s` by ( match_mp_tac rep_in \\ rw[EXTENSION, Abbr`s`] \\ metis_tac[] )
  \\ fs[Abbr`s`]
  \\ TRY (goal_assum(first_assum o mp_then Any mp_tac))
  \\ TRY (AP_TERM_TAC \\ simp[EXTENSION])
  \\ metis_tac[]
QED

Theorem sing_env:
  c ∈ chu_objects w ∧ SING (c.env) ⇒ c ≃ cfbot w (image c) -: w
Proof
  rw[]
  \\ `image c ⊆ w` by (
    fs[chu_objects_def, wf_def, image_def, SUBSET_DEF, PULL_EXISTS] \\ rw[] )
  \\ `swap c ≃ cf1 w (image c) -: w` suffices_by
        metis_tac[swap_swap, homotopy_equiv_swap, swap_in_chu_objects,
                  cf1_in_chu_objects, cfbot_def]
  \\ rewrite_tac[Once (GSYM image_swap)]
  \\ irule sing_agent
  \\ simp[]
QED

Theorem cf0_prod_cf0[simp]:
  cf0 w && cf0 w ≃ cf0 w -: w
Proof
  match_mp_tac empty_agent_nonempty_env
  \\ simp[]
  \\ simp[prod_def]
  \\ simp[cf0_def]
QED

Theorem prod_cfT[simp]:
  c ∈ chu_objects w ⇒ cfT w && c ≅ c -: chu w ∧ c && cfT w ≅ c -: chu w
Proof
  rw[cfT_def, GSYM swap_sum_prod]
  \\ metis_tac[sum_cf0, swap_in_chu_objects, swap_swap, iso_objs_trans, swap_iso, is_category_chu]
QED

val _ = export_theory();
