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
     pred_setTheory helperSetTheory relationTheory listTheory sortingTheory stringTheory
     categoryTheory cf0Theory cf1Theory

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

Theorem chu_iso_bij:
  iso (chu w) f ⇔
    BIJ f.map.map_agent f.dom.agent f.cod.agent ∧
    BIJ f.map.map_env f.cod.env f.dom.env ∧
    f.dom ∈ chu_objects w ∧ f.cod ∈ chu_objects w ∧ is_chu_morphism f.dom f.cod f.map
Proof
  rw[iso_def, iso_pair_def]
  \\ reverse EQ_TAC \\ strip_tac
  >- (
    qmatch_assum_abbrev_tac`BIJ g _.agent _`
    \\ qmatch_assum_abbrev_tac`BIJ g A _`
    \\ qmatch_assum_abbrev_tac`BIJ h _.env _`
    \\ qmatch_assum_abbrev_tac`BIJ h E _`
    \\ qexists_tac`mk_chu_morphism f.cod f.dom
                      <| map_agent := LINV g A; map_env := LINV h E |>`
    \\ conj_asm1_tac
    >- (
      simp[composable_in_def, pre_chu_def]
      \\ fs[is_chu_morphism_def, mk_chu_morphism_def]
      \\ simp[restrict_def]
      \\ imp_res_tac BIJ_LINV_INV
      \\ fs[BIJ_DEF]
      \\ imp_res_tac LINV_DEF
      \\ conj_tac >- metis_tac[SURJ_DEF]
      \\ conj_tac >- metis_tac[SURJ_DEF]
      \\ qx_genl_tac[`b`,`d`]
      \\ strip_tac
      \\ `g (LINV g A b) = b` by metis_tac[]
      \\ `LINV g A b ∈ A` by metis_tac[SURJ_DEF]
      \\ `h (LINV h E d) = d` by metis_tac[]
      \\ `LINV h E d ∈ E` by metis_tac[SURJ_DEF]
      \\ metis_tac[])
    \\ qmatch_assum_abbrev_tac`f ≈> fi -: _`
    \\ `fi ≈> f -:chu w` by fs[composable_in_def,Abbr `fi`]
    \\ simp[compose_in_thm]
    \\ DEP_REWRITE_TAC[compose_thm]
    \\ conj_tac >- fs[composable_in_def]
    \\ simp[chu_comp]
    \\ `fi.dom = f.cod ∧ fi.cod = f.dom` by simp[Abbr`fi`, mk_chu_morphism_def]
    \\ simp[morphism_component_equality, id_in_def, restrict_def]
    \\ simp[pre_chu_def, chu_id_morphism_map_def]
    \\ simp[Abbr`fi`, mk_chu_morphism_def, restrict_def, FUN_EQ_THM]
    \\ imp_res_tac BIJ_LINV_INV
    \\ fs[BIJ_DEF]
    \\ imp_res_tac LINV_DEF
    \\ rw[] \\ metis_tac[SURJ_DEF] )
  \\ qpat_x_assum`_ = id _ -: _`mp_tac
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ simp[]
  \\ DEP_REWRITE_TAC[compose_thm]
  \\ conj_tac >- fs[composable_in_def]
  \\ simp[Once morphism_component_equality]
  \\ imp_res_tac composable_obj \\ fs[] \\ strip_tac
  \\ `g ≈> f -: chu w` by fs[composable_in_def]
  \\ qpat_x_assum`_ = id _ -: _`mp_tac
  \\ DEP_REWRITE_TAC[compose_in_thm]
  \\ simp[]
  \\ simp[Once morphism_component_equality]
  \\ strip_tac
  \\ fs[pre_chu_def, chu_id_morphism_map_def]
  \\ fs[restrict_def, FUN_EQ_THM, is_chu_morphism_def, composable_in_def, pre_chu_def]
  \\ simp[BIJ_IFF_INV]
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

Definition biextensional_def:
  biextensional c ⇔
    (∀a1 a2. a1 ∈ c.agent ∧ a2 ∈ c.agent ∧
            (∀e. e ∈ c.env ⇒ c.eval a1 e = c.eval a2 e)
      ⇒ a1 = a2) ∧
    (∀e1 e2. e1 ∈ c.env ∧ e2 ∈ c.env ∧
             (∀a. a ∈ c.agent ⇒ c.eval a e1 = c.eval a e2)
      ⇒ e1 = e2)
End

(* TODO: prove biextensional iff matrix row/cols all distinct *)

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
  \\ simp[biextensional_def]
  \\ ntac 2 strip_tac
  \\ simp[BIJ_IFF_INV]
  \\ fs[is_chu_morphism_def]
  \\ conj_tac
  >- (
    qexists_tac`g.map.map_agent` \\ fs[]
    \\ imp_res_tac maps_to_in_def
    \\ fs[pre_chu_def, is_chu_morphism_def] )
  \\ qexists_tac`g.map.map_env` \\ fs[]
  \\ imp_res_tac maps_to_in_def
  \\ fs[pre_chu_def, is_chu_morphism_def]
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

Definition min_elt_def:
  min_elt R s = @x. x ∈ s ∧ ∀y. y ∈ s ⇒R x y
End

Theorem min_elt_HD_QSORT_SET_TO_LIST:
  FINITE s ∧ s ≠ ∅ ⇒
    min_elt string_le s = HD (QSORT string_le (SET_TO_LIST s))
Proof
  rw[]
  \\ qspec_then`string_le` mp_tac QSORT_SORTS
  \\ impl_keep_tac >- (
    simp[transitive_def, total_def, string_le_def]
    \\ metis_tac[string_lt_cases, string_lt_trans] )
  \\ rw[SORTS_DEF]
  \\ first_x_assum(qspec_then`SET_TO_LIST s`mp_tac)
  \\ rw[]
  \\ Cases_on`SET_TO_LIST s` \\ fs[]
  >- ( imp_res_tac SET_TO_LIST_CARD \\ rfs[] )
  \\ Cases_on`QSORT string_le (SET_TO_LIST s)` \\ fs[]
  \\ rfs[] \\ fs[]
  \\ rfs[SORTED_EQ]
  \\ simp[min_elt_def]
  \\ SELECT_ELIM_TAC
  \\ imp_res_tac MEM_PERM \\ fs[]
  \\ metis_tac[MEM_SET_TO_LIST, string_lt_antisym, string_le_def, MEM]
QED

Definition biextensional_collapse_def:
  biextensional_collapse c =
    <| world := c.world;
       agent := IMAGE (min_elt (RC (SHORTLEX char_lt)) o (equiv_class (agent_equiv c) c.agent)) c.agent;
       env := IMAGE (min_elt (RC (SHORTLEX char_lt)) o (equiv_class (env_equiv c) c.env)) c.env;
       eval := c.eval |>
End

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

Theorem min_elt_char_lt_in:
  s ≠ ∅ ⇒ min_elt (RC (SHORTLEX char_lt)) s ∈ s
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

Theorem eval_equiv:
  a ∈ c.agent ∧ e ∈ c.env ∧
  a' ∈ equiv_class (agent_equiv c) c.agent a ∧
  e' ∈ equiv_class (env_equiv c) c.env e ⇒
  c.eval a' e' = c.eval a e
Proof
  rw[agent_equiv_def, env_equiv_def]
QED

Theorem biextensional_collapse_biextensional:
  biextensional (biextensional_collapse c)
Proof
  rw[biextensional_def]
  \\ fs[biextensional_collapse_def, PULL_EXISTS] \\ rw[]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[equiv_class_eq]
  \\ simp[]
  >- (
    qmatch_rename_tac`agent_equiv c a1 a2`
    \\ qmatch_asmsub_abbrev_tac`c.eval x1 _ = c.eval x2 _`
    \\ qmatch_asmsub_abbrev_tac`x1 = min_elt _ s1`
    \\ qmatch_asmsub_abbrev_tac`x2 = min_elt _ s2`
    \\ `a1 ∈ s1` by simp[Abbr`s1`, agent_equiv_equiv]
    \\ `a2 ∈ s2` by simp[Abbr`s2`, agent_equiv_equiv]
    \\ `x1 ∈ s1` by (simp[Abbr`x1`] \\ metis_tac[MEMBER_NOT_EMPTY,min_elt_char_lt_in])
    \\ `x2 ∈ s2` by (simp[Abbr`x2`] \\ metis_tac[MEMBER_NOT_EMPTY,min_elt_char_lt_in])
    \\ `agent_equiv c x1 a1`
    by (
      rw[agent_equiv_def]
      \\ match_mp_tac eval_equiv
      \\ qunabbrev_tac`x1`
      \\ qunabbrev_tac`s1`
      \\ DEP_REWRITE_TAC[min_elt_char_lt_in]
      \\ simp[env_equiv_equiv]
      \\ simp[EXTENSION]
      \\ metis_tac[agent_equiv_equiv] )
    \\ `agent_equiv c x1 x2`
    by (
      simp[agent_equiv_def] \\ rw[]
      \\ first_x_assum(qspec_then`e`mp_tac) \\ rw[]
      \\ qmatch_asmsub_abbrev_tac`c.eval x1 (min_elt _ t1)`
      \\ qmatch_asmsub_abbrev_tac`c.eval x1 y1`
      \\ `e ∈ t1` by simp[Abbr`t1`, env_equiv_equiv]
      \\ `y1 ∈ t1` by (simp[Abbr`y1`] \\ metis_tac[MEMBER_NOT_EMPTY,min_elt_char_lt_in])
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
      \\ DEP_REWRITE_TAC[min_elt_char_lt_in]
      \\ simp[env_equiv_equiv]
      \\ simp[EXTENSION]
      \\ metis_tac[agent_equiv_equiv] )
    \\ metis_tac[agent_equiv_equiv])
  \\ qmatch_rename_tac`env_equiv c a1 a2`
  \\ qmatch_asmsub_abbrev_tac`c.eval _ x1 = c.eval _ x2`
  \\ qmatch_asmsub_abbrev_tac`x1 = min_elt _ s1`
  \\ qmatch_asmsub_abbrev_tac`x2 = min_elt _ s2`
  \\ `a1 ∈ s1` by simp[Abbr`s1`, env_equiv_equiv]
  \\ `a2 ∈ s2` by simp[Abbr`s2`, env_equiv_equiv]
  \\ `x1 ∈ s1` by (simp[Abbr`x1`] \\ metis_tac[MEMBER_NOT_EMPTY,min_elt_char_lt_in])
  \\ `x2 ∈ s2` by (simp[Abbr`x2`] \\ metis_tac[MEMBER_NOT_EMPTY,min_elt_char_lt_in])
  \\ `env_equiv c x1 a1`
  by (
    rw[env_equiv_def]
    \\ match_mp_tac eval_equiv
    \\ qunabbrev_tac`x1`
    \\ qunabbrev_tac`s1`
    \\ DEP_REWRITE_TAC[min_elt_char_lt_in]
    \\ simp[agent_equiv_equiv]
    \\ simp[EXTENSION]
    \\ metis_tac[env_equiv_equiv] )
  \\ `env_equiv c x1 x2`
  by (
    simp[env_equiv_def] \\ rw[]
    \\ first_x_assum(qspec_then`a`mp_tac) \\ rw[]
    \\ qmatch_asmsub_abbrev_tac`c.eval (min_elt _ t1) x1`
    \\ qmatch_asmsub_abbrev_tac`c.eval y1 x1`
    \\ `a ∈ t1` by simp[Abbr`t1`, agent_equiv_equiv]
    \\ `y1 ∈ t1` by (simp[Abbr`y1`] \\ metis_tac[MEMBER_NOT_EMPTY,min_elt_char_lt_in])
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
    \\ DEP_REWRITE_TAC[min_elt_char_lt_in]
    \\ simp[agent_equiv_equiv]
    \\ simp[EXTENSION]
    \\ metis_tac[env_equiv_equiv] )
  \\ metis_tac[env_equiv_equiv]
QED

Theorem biextensional_iso:
  biextensional c ∧ c ≅ d -: chu w ⇒ biextensional d
Proof
  rw[iso_objs_thm, chu_iso_bij]
  \\ fs[biextensional_def]
  \\ fs[maps_to_in_def]
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ fs[pre_chu_def]
  \\ fs[is_chu_morphism_def]
  \\ fs[BIJ_IFF_INV]
  \\ metis_tac[]
QED

Theorem biextensional_collapse_in_chu_objects[simp]:
  c ∈ chu_objects w ⇒ biextensional_collapse c ∈ chu_objects w
Proof
  rw[chu_objects_def, biextensional_collapse_def]
  \\ fs[wf_def, PULL_EXISTS] \\ rw[]
  \\ first_x_assum match_mp_tac
  \\ metis_tac[min_elt_char_lt_in, MEMBER_NOT_EMPTY, equiv_class_element,
               agent_equiv_equiv, env_equiv_equiv]
QED

Theorem min_elt_in_equiv_class[simp]:
  R equiv_on s ∧ x ∈ s ⇒
  min_elt (RC (SHORTLEX char_lt)) (equiv_class R s x) ∈ s ∧
  min_elt (RC (SHORTLEX char_lt)) (equiv_class R s x) ∈ equiv_class R s x
Proof
  strip_tac
  \\ `x ∈ equiv_class R s x` by ( simp[equiv_class_element] \\ fs[equiv_on_def] )
  \\ imp_res_tac MEMBER_NOT_EMPTY
  \\ imp_res_tac min_elt_char_lt_in
  \\ fs[]
QED

Theorem equiv_class_min_elt_eq:
  R equiv_on s ∧ x ∈ s⇒
  (equiv_class R s (min_elt (RC (SHORTLEX char_lt)) (equiv_class R s x))) =
  (equiv_class R s x)
Proof
  strip_tac
  \\ `x ∈ equiv_class R s x` by ( simp[equiv_class_element] \\ fs[equiv_on_def] )
  \\ imp_res_tac MEMBER_NOT_EMPTY
  \\ imp_res_tac min_elt_char_lt_in
  \\ DEP_REWRITE_TAC[equiv_class_eq]
  \\ fs[]
  \\ fs[equiv_on_def]
QED

(*
Theorem biextensional_iff_iso_collapse:
  c ∈ chu_objects w ⇒
  (biextensional c ⇔ c ≅ (biextensional_collapse c) -: chu w)
Proof
  strip_tac
  \\ reverse EQ_TAC
  >- metis_tac[biextensional_iso, biextensional_collapse_biextensional,
               iso_objs_sym, is_category_chu]
  \\ simp[iso_objs_thm]
  \\ rw[biextensional_def]
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
    \\ simp[restrict_def]
    \\ conj_tac >- ( reverse(rw[]) >- metis_tac[] \\ simp[Abbr`f`] )
    \\ conj_tac >- ( rw[Abbr`f`] \\ metis_tac[] )
    \\ reverse(rw[]) >- metis_tac[]
    \\ simp[Abbr`f`]
    \\ DEP_REWRITE_TAC[equiv_class_min_elt_eq]
    \\ simp[]
    \\ qmatch_abbrev_tac`_ = c.eval a' _`
    \\ `a' ∈ equiv_class (agent_equiv c) c.agent a` by ( simp[Abbr`a'`] )
    \\ fs[agent_equiv_def] )
  \\ simp[chu_iso_bij]
  \\ fs[maps_to_in_def, pre_chu_def]
  \\ fs[mk_chu_morphism_def]
*)

val _ = export_theory();
