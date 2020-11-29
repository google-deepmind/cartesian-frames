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


val _ = export_theory();
