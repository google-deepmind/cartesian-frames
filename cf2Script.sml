open HolKernel boolLib bossLib Parse dep_rewrite
     pred_setTheory categoryTheory cf1Theory

val _ = new_theory"cf2";

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

val _ = export_theory();
