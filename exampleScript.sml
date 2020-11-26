open HolKernel boolLib bossLib boolSimps Parse
  pred_setTheory stringTheory stringLib
  cf0Theory cf1Theory

val _ = new_theory"example";

Definition runs_cf1_def:
  runs_cf1 = <| agent := { "u"; "n" }; env := { "r"; "s" };
                world := {"ur"; "us"; "nr"; "ns"};
                eval := λa e. a ++ e |>
End

Theorem sup_closure_example:
  sup_closure runs_cf1.world {{"ur"; "us"};{"nr";"ns"}} =
  {{"ur"; "us"};{"nr";"ns"};
   {"ur";"us";"nr"};{"ur";"us";"ns"};{"nr";"ns";"ur"};{"nr";"ns";"us"};
   runs_cf1.world}
Proof
  rw[SET_EQ_SUBSET]
  >- (
    rw[sup_closure_def, runs_cf1_def, SUBSET_DEF, SET_EQ_SUBSET]
    \\ fsrw_tac[DNF_ss][]
    \\ metis_tac[] )
  \\ rw[sup_closure_def]
  \\ srw_tac[DNF_ss][]
  \\ EVAL_TAC
QED

Theorem sub_closure_example:
  sub_closure runs_cf1.world {{"ur"; "us"};{"nr";"ns"}} =
  {{"ur"; "us"};{"nr";"ns"};
   {"ur"};{"us"};{"nr"};{"ns"};{}}
Proof
  rw[SET_EQ_SUBSET]
  \\ TRY (
    rw[sub_closure_def, runs_cf1_def]
    \\ fsrw_tac[DNF_ss][]
    \\ NO_TAC)
  \\ rw[sub_closure_def, runs_cf1_def, SUBSET_DEF]
  \\ spose_not_then strip_assume_tac \\ fs[EXTENSION]
  \\ metis_tac[]
QED

Theorem runs1_ensure:
  ensure runs_cf1 = sup_closure runs_cf1.world {{"ur"; "us"}; {"nr"; "ns"}}
Proof
  rw[ensure_def, runs_cf1_def, sup_closure_example]
  \\ rw[SET_EQ_SUBSET, SUBSET_DEF]
  \\ fsrw_tac[DNF_ss][] \\ metis_tac[]
QED

Theorem runs1_prevent:
  prevent runs_cf1 = sub_closure runs_cf1.world {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[prevent_def, runs_cf1_def, sub_closure_example]
  \\ rw[SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][]
  \\ Cases_on`x = {}` \\ fs[]
  \\ Cases_on`x` \\ fsrw_tac[DNF_ss][] \\ rw[INSERT_EQ_SING]
  \\ Cases_on`t` \\ fsrw_tac[DNF_ss][] \\ rw[INSERT_EQ_SING]
  \\ fs[EXTENSION] \\ metis_tac[]
QED


Theorem runs1_ctrl:
  ctrl runs_cf1 = {{"ur";"us"};{"nr";"ns"}}
Proof
  rw[ctrl_def, runs1_prevent, runs1_ensure, sub_closure_example, sup_closure_example]
  \\ rw[runs_cf1_def]
  \\ rw[EXTENSION] \\ metis_tac[]
QED

Definition runs_cf2_def:
  runs_cf2 = <| agent := {"u";"n";"run";"sun"};
                env := {"r";"s"};
                world := runs_cf1.world;
                eval := λa e. (if LENGTH a < 2 then EL 0 a else
                               if EL 0 e = EL 0 a then EL 1 a else EL 2 a)::e |>
End

Theorem runs2_ctrl:
  ctrl runs_cf2 = {{"ur";"us"};{"nr";"ns"};{"ur";"ns"};{"nr";"us"}}
Proof
  rw[ctrl_def, ensure_def, prevent_def, runs_cf2_def, runs_cf1_def, SUBSET_DEF]
  \\ rw[Once EXTENSION]
  \\ EQ_TAC \\ rw[] \\ fs[]
  \\ spose_not_then strip_assume_tac
  \\ fsrw_tac[DNF_ss][]
  \\ fs[Once EXTENSION]
  \\ metis_tac[]
QED

Definition runs_cf3_def:
  runs_cf3 = runs_cf2 with <| env := "m" INSERT runs_cf2.env;
                              world := "m" INSERT runs_cf2.world;
                              eval := λa e. if e = "m" then "m" else runs_cf2.eval a e |>
End

Theorem runs3_ensure:
  ensure runs_cf3 =
    sup_closure runs_cf3.world {{"ur";"us";"m"};{"nr";"ns";"m"};{"ur";"ns";"m"};{"nr";"us";"m"}}
Proof
  rw[ensure_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[sup_closure_def]
  \\ rw[Once EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w` \\ Cases_on`x ⊆ w` \\ fs[]
  \\ EQ_TAC \\ rw[] \\ fsrw_tac[DNF_ss][]
QED

Theorem runs3_prevent:
  prevent runs_cf3 =
    sub_closure runs_cf3.world {{"ur";"us"};{"nr";"ns"};{"ur";"ns"};{"nr";"us"}}
Proof
  rw[prevent_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[sub_closure_def]
  \\ rw[Once EXTENSION]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w` \\ Cases_on`x ⊆ w` \\ fs[]
  \\ EQ_TAC >- (
    rw[] \\ fsrw_tac[DNF_ss][]
    \\ fsrw_tac[DNF_ss][SUBSET_DEF]
    \\ spose_not_then strip_assume_tac \\ fsrw_tac[DNF_ss][Once EXTENSION, Abbr`w`]
    \\ metis_tac[] )
  \\ strip_tac \\ rpt BasicProvers.var_eq_tac
  THENL (map (exists_tac o fromMLstring) ["n", "u", "sun", "run"])
  \\ rw[] \\ CCONTR_TAC \\ fs[SUBSET_DEF] \\ res_tac \\ fs[]
QED

fun tails [] = []
  | tails (x::y) = (x,y) :: tails y

val envs = ["m","us","ur","ns","nr"]
val ineqs =
  map (fn (x, r) =>
         map (fn y => EVAL(mk_eq(fromMLstring x, fromMLstring y))) r)
      (tails envs) |> List.concat

Theorem runs3_ctrl:
  ctrl runs_cf3 = ∅
Proof
  rw[ctrl_def, runs3_ensure, runs3_prevent]
  \\ rw[sup_closure_def, sub_closure_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ rw[GSYM DISJOINT_DEF]
  \\ rw[IN_DISJOINT]
  \\ qmatch_goalsub_abbrev_tac`x ⊆ w`
  \\ Cases_on`x ⊆ w` \\ fs[]
  \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[Abbr`w`] \\ fs[SUBSET_DEF]
  \\ metis_tac ineqs
QED

Theorem runs1_obs:
  obs runs_cf1 = union_closure {runs_cf1.world}
Proof
  rw[union_closure_sing, obs_def, EXTENSION, SUBSET_DEF, runs_cf1_def, ifs_def]
  \\ rw[Once EQ_IMP_THM]
  \\ fsrw_tac[DNF_ss][]
  \\ metis_tac[]
QED

Theorem wf_runs2[simp]:
  wf runs_cf2
Proof
  rw[wf_def, runs_cf2_def, runs_cf1_def]
QED

Theorem wf_runs3[simp]:
  wf runs_cf3
Proof
  rw[wf_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
QED

Theorem runs2_obs:
  obs runs_cf2 = union_closure {{"ur";"nr"}; {"us";"ns"}}
Proof
  qmatch_goalsub_abbrev_tac`union_closure s`
  \\ `union_closure s = {{}; runs_cf1.world} ∪ s`
  by (
    rw[Abbr`s`, union_closure_def, runs_cf1_def]
    \\ rw[Once EXTENSION]
    \\ Cases_on`x = {}` \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`x = {"us";"ns"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"us";"ns"}}` \\ simp[])
    \\ Cases_on`x = {"ur";"nr"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"ur";"nr"}}` \\ simp[])
    \\ Cases_on`x = {"ur";"us";"nr";"ns"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"ur";"nr"};{"us";"ns"}}` \\ simp[] \\ simp[EXTENSION] \\ metis_tac[])
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ Cases_on`s` \\ fs[] \\ rw[] \\ fs[]
    \\ Cases_on`t` \\ fs[] \\ rw[] \\ fs[] \\ rw[] \\ fs[] \\ rw[]
    \\ fs[EXTENSION] \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ once_rewrite_tac[SET_EQ_SUBSET]
  \\ reverse conj_asm2_tac >- (
    simp[SUBSET_DEF, GSYM CONJ_ASSOC]
    \\ conj_asm1_tac >- simp[obs_empty]
    \\ conj_tac >- (
      first_assum(mp_then Any mp_tac obs_compl)
      \\ simp[runs_cf2_def] )
    \\ pop_assum kall_tac
    \\ simp[Abbr`s`]
    \\ rw[obs_def] \\ TRY (rw[runs_cf2_def, runs_cf1_def, SUBSET_DEF] \\ NO_TAC)
    \\ rw[ifs_def]
    \\ fs[runs_cf2_def, runs_cf1_def] \\ rw[]
    \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
  \\ rw[SUBSET_DEF]
  \\ CCONTR_TAC \\ fs[]
  \\ qpat_x_assum`x ∈ _`mp_tac
  \\ rw[obs_def, runs_cf2_def]
  \\ Cases_on`x ⊆ runs_cf1.world` \\ fs[]
  \\ fs[Abbr`s`]
  \\ Cases_on`x = {"ur"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"nr"}`
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur"}`
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur";"ns"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"ns"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"nr"}`
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"ur";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"us";"nr"}`
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ `F` suffices_by rw[]
  \\ qpat_x_assum`x ⊆ _`mp_tac
  \\ fs[runs_cf1_def]
  \\ simp[GSYM IN_POW]
  \\ simp[POW_EQNS]
  \\ fs[INSERT_COMM]
QED

Theorem runs3_obs:
  obs runs_cf3 = union_closure {{"ur";"nr"};{"us";"ns"};{"m"}}
Proof
  qmatch_goalsub_abbrev_tac`union_closure s`
  \\ `union_closure s = s ∪
        {{}; runs_cf3.world; {"ur";"nr";"us";"ns"}; {"ur";"nr";"m"}; {"us";"ns";"m"}}`
  by (
    rw[Abbr`s`, runs_cf3_def, runs_cf2_def, runs_cf1_def]
    \\ rw[Once EXTENSION]
    \\ rw[union_closure_def]
    \\ Cases_on`x = {}` \\ fsrw_tac[DNF_ss][]
    \\ Cases_on`x = {"m"}` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{{"m"}}` \\ simp[])
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{s}` \\ simp[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (qexists_tac`{s}` \\ simp[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ t`
      \\ qexists_tac`t`
      \\ simp[Abbr`s`,Abbr`t`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ {s1;s2;s3}`
      \\ qexists_tac`{s1;s2}`
      \\ simp[Abbr`s`,Abbr`s1`,Abbr`s2`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s ∨ _`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ {s1;s2;s3}`
      \\ qexists_tac`{s1;s3}`
      \\ simp[Abbr`s`,Abbr`s1`,Abbr`s3`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ qmatch_goalsub_abbrev_tac`x = s`
    \\ Cases_on`x = s` \\ fsrw_tac[DNF_ss][]
    >- (
      qmatch_goalsub_abbrev_tac`_ ⊆ {s1;s2;s3}`
      \\ qexists_tac`{s2;s3}`
      \\ simp[Abbr`s`,Abbr`s2`,Abbr`s3`]
      \\ simp[EXTENSION] \\ PROVE_TAC[])
    \\ qunabbrev_tac`s`
    \\ rw[GSYM IN_POW]
    \\ simp[POW_EQNS]
    \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[] \\ fs[EXTENSION]
    \\ metis_tac[])
  \\ pop_assum SUBST1_TAC
  \\ qunabbrev_tac `s`
  \\ simp[SimpRHS, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ once_rewrite_tac[SET_EQ_SUBSET]
  \\ reverse conj_asm2_tac >- (
    simp[SUBSET_DEF, GSYM CONJ_ASSOC]
    \\ `∅ ∈ obs runs_cf3` by simp[obs_empty]
    \\ first_assum(mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def]
    \\ strip_tac
    \\ `{"m"} ∈ obs runs_cf3`
    by (
      simp[obs_def]
      \\ conj_tac >- EVAL_TAC
      \\ rpt gen_tac \\ strip_tac
      \\ qexists_tac`a1` \\ simp[]
      \\ simp[ifs_def]
      \\ simp[runs_cf3_def, runs_cf2_def]
      \\ rw[] )
    \\ first_assum (mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def, INSERT_COMM]
    \\ strip_tac
    \\ `{"ur";"nr"} ∈ obs runs_cf3`
    by (
      simp[obs_def]
      \\ conj_tac >- EVAL_TAC
      \\ rpt gen_tac \\ strip_tac
      \\ simp[ifs_def, runs_cf3_def, runs_cf2_def]
      \\ fs[runs_cf3_def, runs_cf2_def, runs_cf1_def]
      \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
    \\ first_assum (mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def, INSERT_COMM]
    \\ strip_tac
    \\ `{"us";"ns"} ∈ obs runs_cf3`
    by (
      simp[obs_def]
      \\ conj_tac >- EVAL_TAC
      \\ rpt gen_tac \\ strip_tac
      \\ simp[ifs_def, runs_cf3_def, runs_cf2_def]
      \\ fs[runs_cf3_def, runs_cf2_def, runs_cf1_def]
      \\ TRY(qexists_tac`"u"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"n"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"run"` \\ rw[] \\ fs[] \\ NO_TAC)
      \\ TRY(qexists_tac`"sun"` \\ rw[] \\ fs[] \\ NO_TAC))
    \\ first_assum (mp_then Any mp_tac obs_compl)
    \\ simp[]
    \\ simp[Once runs_cf3_def, runs_cf2_def, runs_cf1_def, INSERT_COMM])
  \\ rw[SUBSET_DEF]
  \\ CCONTR_TAC \\ fs[]
  \\ qpat_x_assum`x ∈ _`mp_tac
  \\ rw[obs_def, runs_cf3_def, runs_cf2_def, runs_cf1_def]
  \\ simp[Once (GSYM IMP_DISJ_THM)]
  \\ simp[GSYM IN_POW]
  \\ simp[POW_EQNS]
  \\ fs[INSERT_COMM]
  \\ Cases_on`x = {"ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"nr"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ur";"ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"ns"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"us";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"ns";"us";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ fs[INSERT_COMM, GSYM DISJ_ASSOC]
  \\ Cases_on`x = {"m"; "ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "us"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"u"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "ur"}` \\ fs[]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m"; "ns";"nr"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"ur"}` \\ fs[]
  >- (
    qexists_tac`"run"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"ur";"ns"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"nr"}` \\ fs[]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"n"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"ur";"ns"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"us";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"n"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"ns";"ur";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"run"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
  \\ Cases_on`x = {"m";"ns";"us";"nr"}` \\ fs[INSERT_COMM]
  >- (
    qexists_tac`"u"` \\ qexists_tac`"sun"`
    \\ simp[ifs_def] \\ rw[]
    \\ CCONTR_TAC \\ fs[] \\ rw[]
    \\ pop_assum mp_tac \\ simp[] \\ fs[]
    \\ TRY(qexists_tac`"s"` \\ simp[] \\ NO_TAC)
    \\ TRY(qexists_tac`"r"` \\ simp[] \\ NO_TAC))
QED

Definition runs_cf4_def:
  runs_cf4 = <| world := runs_cf1.world; agent := {1}; env := runs_cf1.world; eval := λa e. e |>
End

Definition runs_cf5_def:
  runs_cf5 = <| world := runs_cf1.world; env := {1}; agent := runs_cf1.world; eval := λa e. a |>
End

(* TODO: facts about runs_cf4, runs_cf5 *)


Definition test_world_def:
  test_world = "F" INSERT BIGUNION (IMAGE (λg. {g;g++"+";g++"-"}) {"A";"B";"C";"D"})
End

Theorem test_world_eq = EVAL ``test_world``

Definition test_today_def:
  test_today = <| world := test_world;
                  env := {"t";"d";"o"};
                  agent := {"s";"i"};
                  eval := λa e. if a = "i" then "C+" else
                                if e = "t" then "A-" else
                                if e = "d" then "B+" else "D-" |>
End

Definition test_yesterday_def:
  test_yesterday = <| world := test_world;
                      env := test_today.env;
                      agent := "c" INSERT test_today.agent;
                      eval := λa e. if a = "c" then "A+" else test_today.eval a e |>
End

Definition test_demanding_def:
  test_demanding = <| world := test_world;
                      env := test_today.env DELETE "t";
                      agent := test_today.agent;
                      eval := test_today.eval |>
End

Theorem morphism_today_yesterday:
  is_chu_morphism test_today test_yesterday <| map_env := I; map_agent := I |>
Proof
  simp[is_chu_morphism_def]
  \\ rw[test_today_def, test_yesterday_def]
QED

Theorem morphism_today_demanding:
  is_chu_morphism test_today test_demanding <| map_env := I; map_agent := I |>
Proof
  simp[is_chu_morphism_def]
  \\ rw[test_today_def, test_demanding_def]
QED

Theorem no_morphisms_yesterday_demanding:
  ¬is_chu_morphism test_yesterday test_demanding m ∧
  ¬is_chu_morphism test_demanding test_yesterday m
Proof
  Cases_on`m`
  \\ qmatch_goalsub_rename_tac`chu_morphism_map f g`
  \\ simp[is_chu_morphism_def]
  \\ conj_tac
  \\ (qmatch_abbrev_tac`a ∨ b` \\ Cases_on`a = T` \\ fs[Abbr`a`, Abbr`b`]
      >- metis_tac[] \\ disj2_tac)
  \\ (qmatch_abbrev_tac`a ∨ b` \\ Cases_on`a = T` \\ fs[Abbr`a`, Abbr`b`]
      >- metis_tac[] \\ disj2_tac)
  \\ fs[GSYM IMP_DISJ_THM]
  \\ fs[test_yesterday_def, test_demanding_def, test_today_def]
  >- (
    qexists_tac`"c"` \\ simp[]
    \\ qexists_tac`"d"` \\ rw[] )
  \\ qexists_tac`if f "i" = "i" then "s" else "i"`
  \\ qexists_tac`"t"`
  \\ simp[]
  \\ IF_CASES_TAC \\ simp[]
  \\ rw[]
QED

Definition handshake_def:
  handshake = <| world := {0; 1};
                 agent := {0; 1};
                 env := {0; 1};
                 eval := arithmetic$* |>
End

Definition bothsing_def:
  bothsing = <| world := {0};
                agent := {0};
                env := {0};
                eval := K (K 0) |>
End

Theorem morphism_handshake_bothsing:
  is_chu_morphism handshake bothsing <| map_agent := K 0; map_env := K 0 |>
Proof
  simp[is_chu_morphism_def, handshake_def, bothsing_def]
QED

Theorem morphism_bothsing_handshake:
  is_chu_morphism bothsing handshake <| map_agent := K 0; map_env := K 0 |>
Proof
  simp[is_chu_morphism_def, handshake_def, bothsing_def]
QED

val _ = export_theory();
