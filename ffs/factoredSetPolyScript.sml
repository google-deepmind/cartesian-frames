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
     bagTheory containerTheory pred_setTheory pairTheory
     ringRealTheory fieldRealTheory gbagTheory multipolyTheory
     extrealTheory measureTheory probabilityTheory
     partitionTheory factoredSetTheory

val _ = new_theory "factoredSetPoly";

open listTheory sortingTheory ringMapTheory monoidMapTheory integralDomainTheory ringTheory ringIdealTheory ringUnitTheory polyRingTheory ringDividesTheory polynomialTheory polyDividesTheory polyDivisionTheory

Theorem PERM_BAG_TO_LIST_UNION_APPEND:
  !b1 b2. FINITE_BAG b1 /\ FINITE_BAG b2 ==>
  PERM (BAG_TO_LIST (BAG_UNION b1 b2))
       (BAG_TO_LIST b1 ++ BAG_TO_LIST b2)
Proof
  rpt strip_tac
  \\ rewrite_tac[GSYM PERM_LIST_TO_BAG]
  \\ simp[LIST_TO_BAG_APPEND]
  \\ simp[BAG_TO_LIST_INV]
QED

Theorem LIST_REL_collect:
  !R l1 l2. LENGTH l1 <= LENGTH l2 ==>
    ?l1a l2a l1b l2b.
      PERM l1 (l1a ++ l1b) /\
      PERM l2 (l2a ++ l2b) /\
      LIST_REL R l1a l2a /\
      !x y. MEM x l1b /\ MEM y l2b ==> ~R x y
Proof
  qx_gen_tac`P`
  \\ Induct \\ simp[]
  >- ( gen_tac \\ qexists_tac`l2` \\ simp[] )
  \\ gen_tac
  \\ rpt strip_tac
  \\ Cases_on`?g. MEM g l2 /\ P h g`
  >- (
    fs[]
    \\ drule (#1 (EQ_IMP_RULE MEM_SPLIT_APPEND_first))
    \\ strip_tac
    \\ first_x_assum SUBST_ALL_TAC
    \\ first_x_assum(qspec_then`pfx++sfx`mp_tac)
    \\ impl_tac >- fs[]
    \\ strip_tac
    \\ qexistsl_tac[`h::l1a`,`g::l2a`,`l1b`,`l2b`]
    \\ conj_tac
    >- (
      rewrite_tac[APPEND]
      \\ rewrite_tac[PERM_CONS_IFF]
      \\ simp[] )
    \\ conj_tac
    >- (
      ONCE_REWRITE_TAC[rich_listTheory.CONS_APPEND]
      \\ rewrite_tac[APPEND_NIL]
      \\ irule PERM_TRANS
      \\ qexists_tac`[g] ++ pfx ++ sfx`
      \\ conj_tac
      >- ( rewrite_tac[PERM_SWAP_L_AT_FRONT] \\ simp[] )
      \\ simp[] )
    \\ simp[] )
  \\ first_x_assum(qspec_then`l2`mp_tac)
  \\ impl_tac >- simp[] \\ strip_tac
  \\ qexistsl_tac[`l1a`,`l2a`,`h::l1b`,`l2b`]
  \\ simp[GSYM CONS_PERM]
  \\ dsimp[]
  \\ rpt strip_tac
  \\ fs[]
  \\ metis_tac[MEM_PERM, MEM_APPEND]
QED

Theorem ring_product_element[simp]:
  Ring r /\ SET_OF_BAG b SUBSET r.carrier /\ FINITE_BAG b ==>
  GBAG r.prod b IN r.carrier
Proof
  strip_tac
  \\ `r.carrier = r.prod.carrier` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ irule GBAG_in_carrier
  \\ simp[]
  \\ metis_tac[Ring_def]
QED

Theorem ring_subproduct_divides:
  Ring r /\ s <= b /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET r.carrier ==>
  ring_divides r (GBAG r.prod s) (GBAG r.prod b)
Proof
  rw[ring_divides_def]
  \\ qexists_tac`GBAG r.prod (b - s)`
  \\ conj_asm1_tac
  >- (
    irule ring_product_element
    \\ fs[SUBSET_DEF, FINITE_BAG_DIFF]
    \\ fs[BAG_IN, BAG_INN, BAG_DIFF] )
  \\ DEP_REWRITE_TAC[GSYM GBAG_UNION]
  \\ simp[FINITE_BAG_DIFF]
  \\ conj_tac
  >- (
    conj_tac >- metis_tac[Ring_def]
    \\ conj_tac >- metis_tac[FINITE_SUB_BAG]
    \\ fs[SUBSET_DEF]
    \\ fs[BAG_IN, BAG_INN, BAG_DIFF, SUB_BAG] )
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[BAG_UNION_DIFF]
QED

Theorem ring_product_choose_associates:
  Ring r ==>
  !as u xs. FINITE_BAG xs /\ SET_OF_BAG xs SUBSET r.carrier /\
            as SUBSET r.carrier /\ Unit r u ==>
            ?v ys.
              r.prod.op u (GBAG r.prod xs) =
              r.prod.op v (GBAG r.prod ys) /\
              FINITE_BAG ys /\ SET_OF_BAG ys SUBSET r.carrier /\ Unit r v /\
              BAG_CARD ys = BAG_CARD xs /\
              (!y. BAG_IN y ys ==> ?x. BAG_IN x xs /\ ring_associates r x y) /\
              (!a y. a IN as /\ BAG_IN y ys /\ ring_associates r a y
                     ==> y IN as)
Proof
  rpt strip_tac
  \\ ntac 4 (pop_assum mp_tac)
  \\ qid_spec_tac`xs`
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  >- ( qexists_tac`u` \\ qexists_tac`{||}` \\ simp[] )
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ fs[SET_OF_BAG_INSERT]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ Cases_on`?a. a IN as /\ ring_associates r a e`
  >- (
    fs[]
    \\ pop_assum mp_tac
    \\ simp[Once ring_associates_def]
    \\ strip_tac
    \\ qexists_tac`r.prod.op v ( |/ s )`
    \\ qexists_tac`BAG_INSERT a ys`
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ simp[]
    \\ `u * (e * GBAG r.prod xs) = e * (u * GBAG r.prod xs)`
    by simp[GSYM ring_mult_assoc, ring_mult_comm]
    \\ pop_assum SUBST1_TAC \\ simp[]
    \\ simp[Once ring_mult_comm]
    \\ simp[ring_mult_assoc, ring_unit_inv_element]
    \\ simp[SET_OF_BAG_INSERT]
    \\ simp[ring_unit_mult_unit, ring_unit_has_inv]
    \\ simp[BAG_CARD_THM]
    \\ reverse conj_tac >- (
      reverse conj_tac >- metis_tac[]
      \\ dsimp[]
      \\ simp[ring_associates_def]
      \\ disj1_tac
      \\ qexists_tac`|/ s`
      \\ simp[ring_unit_inv_element, GSYM ring_mult_assoc, ring_unit_has_inv]
      \\ simp[ring_unit_linv] )
    \\ AP_TERM_TAC
    \\ simp[GSYM ring_mult_assoc, ring_unit_inv_element]
    \\ simp[ring_unit_linv]
    \\ simp[ring_mult_comm] )
  \\ qexists_tac`v`
  \\ qexists_tac`BAG_INSERT e ys`
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[SET_OF_BAG_INSERT, BAG_CARD_THM]
  \\ reverse conj_tac >- metis_tac[ring_associates_refl]
  \\ simp[GSYM ring_mult_assoc, ring_mult_comm]
  \\ simp[ring_mult_assoc]
QED

Theorem ring_associates_zero:
  Ring r /\ x IN r.carrier ==>
  (ring_associates r (r.sum.id) x <=> x = r.sum.id) /\
  (ring_associates r x r.sum.id <=> x = r.sum.id)
Proof
  strip_tac
  \\ conj_asm1_tac
  >- (
    reverse(rw[EQ_IMP_THM])
    >- ( irule ring_associates_refl \\ simp[] )
    \\ fs[ring_associates_def]
    \\ pop_assum(assume_tac o SYM) \\ fs[]
    \\ `|/ s * (s * x) = |/ s * r.sum.id` by metis_tac[]
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ simp[ring_unit_inv_element, GSYM ring_mult_assoc]
    \\ simp[ring_unit_linv] )
  \\ irule EQ_TRANS
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ metis_tac[ring_associates_sym, ring_zero_element]
QED

Theorem ring_associates_unit:
  Ring r /\ x IN r.carrier /\ Unit r u /\ ring_associates r x u ==>
  Unit r x
Proof
  rw[ring_associates_def]
  \\ irule ring_unit_mult_unit
  \\ simp[]
QED

Theorem ring_associates_prime:
  Ring r /\ x IN r.carrier /\ p IN r.carrier /\
  ring_prime r p /\ ring_associates r x p ==>
  ring_prime r x
Proof
  rw[ring_prime_def]
  \\ drule ring_associates_divides
  \\ disch_then drule \\ simp[]
  \\ disch_then drule \\ strip_tac
  \\ `ring_associates r p x` by metis_tac[ring_associates_sym]
  \\ metis_tac[ring_associates_divides]
QED

Theorem ring_associates_coset:
  !r x y. Ring r /\ ring_associates r x y /\ y IN r.carrier ==>
          x * r.carrier = y * r.carrier
Proof
  rw[subgroupTheory.coset_def, EXTENSION, ring_associates_def]
  \\ rw[EQ_IMP_THM]
  >- (
    qexists_tac`s * z`
    \\ simp[]
    \\ simp[ring_mult_assoc]
    \\ simp[Once ring_mult_comm]
    \\ simp[ring_mult_assoc]
    \\ AP_TERM_TAC
    \\ simp[Once ring_mult_comm] )
  \\ qexists_tac`z * |/ s`
  \\ simp[ring_unit_inv_element]
  \\ `s IN r.carrier /\ |/ s IN r.carrier` by simp[ring_unit_inv_element]
  \\ simp[Once ring_mult_comm, SimpRHS]
  \\ simp[ring_mult_assoc]
  \\ simp[Once ring_mult_comm]
  \\ AP_TERM_TAC
  \\ simp[GSYM ring_mult_assoc]
  \\ simp[ring_unit_linv]
QED

Theorem integral_domain_associates_coset:
  IntegralDomain r /\ x IN r.carrier /\ y IN r.carrier ==>
  (ring_associates r x y <=> x * r.carrier = y * r.carrier)
Proof
  strip_tac
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ eq_tac >- metis_tac[ring_associates_coset]
  \\ rw[SET_EQ_SUBSET, SUBSET_DEF, subgroupTheory.coset_def, PULL_EXISTS]
  \\ rw[ring_associates_def]
  \\ `∃z. x = y * z /\ z IN r.carrier`
  by metis_tac[ring_mult_rone, ring_one_element]
  \\ rw[]
  \\ Cases_on`y = #0` \\ simp[]
  >- ( qexists_tac`#1` \\ simp[] )
  \\ qexists_tac`z`
  \\ simp[ring_mult_comm]
  \\ first_x_assum(qspec_then`#1`mp_tac)
  \\ simp[] \\ strip_tac
  \\ `y * #1 = y * (z * z')` by metis_tac[ring_mult_rone, ring_mult_assoc]
  \\ `#1 IN r.carrier` by simp[]
  \\ `z * z' IN r.carrier` by simp[]
  \\ `#1 = z * z'` by metis_tac[integral_domain_mult_lcancel]
  \\ metis_tac[ring_unit_property]
QED

Theorem integral_domain_product_eq_zero:
  !r b. IntegralDomain r /\ FINITE_BAG b /\ SET_OF_BAG b SUBSET r.carrier ==>
  (GBAG r.prod b = r.sum.id <=> BAG_IN r.sum.id b)
Proof
  ntac 3 strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac STRONG_FINITE_BAG_INDUCT
  \\ rw[]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ fs[SUBSET_DEF]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ fs[]
  \\ conj_asm1_tac >- metis_tac[Ring_def]
  \\ fs[IntegralDomain_def]
  \\ first_x_assum(qspecl_then[`e`,`GBAG r.prod b`]mp_tac)
  \\ simp[]
  \\ impl_keep_tac
  >- (
    `r.carrier = r.prod.carrier` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ irule GBAG_in_carrier
    \\ simp[SUBSET_DEF] )
  \\ simp[]
  \\ metis_tac[]
QED

Theorem integral_domain_primes_divide_primes:
  IntegralDomain r /\
  ring_associates r (GBAG r.prod qs) (GBAG r.prod ps) /\
  FINITE_BAG ps /\ FINITE_BAG qs /\
  BAG_EVERY (\p. p IN R /\ ring_prime r p /\ p <> #0 /\ ~Unit r p) ps /\
  BAG_EVERY (\p. p IN R /\ ring_prime r p /\ p <> #0 /\ ~Unit r p) qs /\
  ss <= ps
  ==>
  ?ls.
    set ls SUBSET r.carrier /\
    LIST_REL (ring_associates r) (BAG_TO_LIST ss) ls /\
    LIST_TO_BAG ls <= qs
Proof
  rw[]
  \\ drule integral_domain_prime_factors_unique
  \\ disch_then(qspecl_then[`BAG_TO_LIST qs`, `BAG_TO_LIST ps`]mp_tac)
  \\ impl_tac
  >- ( simp[BAG_TO_LIST_INV] \\ fs[BAG_EVERY] )
  \\ strip_tac
  \\ drule SUB_BAG_DIFF_EQ
  \\ strip_tac
  \\ qhdtm_x_assum`PERM`mp_tac
  \\ pop_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`BAG_UNION ss st`
  \\ strip_tac
  \\ `PERM (BAG_TO_LIST (BAG_UNION ss st)) (BAG_TO_LIST ss ++ BAG_TO_LIST st)`
  by (
    irule PERM_BAG_TO_LIST_UNION_APPEND
    \\ simp[Abbr`st`, FINITE_BAG_DIFF]
    \\ metis_tac[FINITE_SUB_BAG] )
  \\ `PERM l3 (BAG_TO_LIST ss ++ BAG_TO_LIST st)`
  by metis_tac[PERM_TRANS, PERM_SYM]
  \\ drule LIST_REL_PERM
  \\ disch_then drule
  \\ rw[LIST_REL_SPLIT2]
  \\ qexists_tac`ys1`
  \\ conj_tac
  >- (
    fs[LIST_REL_EL_EQN, SUBSET_DEF]
    \\ rw[MEM_EL]
    \\ fs[ring_associates_def]
    \\ ntac 2 (first_x_assum(qspec_then`n`mp_tac))
    \\ simp[] \\ rpt strip_tac \\ simp[]
    \\ irule ring_mult_element
    \\ `Ring r` by metis_tac[IntegralDomain_def]
    \\ simp[]
    \\ `MEM (EL n (BAG_TO_LIST ss)) (BAG_TO_LIST ss)`
    by metis_tac[MEM_EL]
    \\ `BAG_IN (EL n (BAG_TO_LIST ss)) ss`
    by metis_tac[MEM_BAG_TO_LIST, FINITE_SUB_BAG]
    \\ `BAG_IN (EL n (BAG_TO_LIST ss)) ps`
    by fs[BAG_IN, BAG_INN, SUB_BAG]
    \\ fs[BAG_EVERY])
  \\ conj_tac
  >- (
    fs[LIST_REL_EL_EQN]
    \\ rw[] \\ gs[]
    \\ irule ring_associates_sym
    \\ fs[BAG_EVERY]
    \\ fs[IntegralDomain_def]
    \\ `BAG_IN (EL n (BAG_TO_LIST ss)) ss` by
      metis_tac[MEM_BAG_TO_LIST, FINITE_SUB_BAG, MEM_EL]
    \\ fs[SUB_BAG, BAG_IN] )
  \\ `LIST_TO_BAG (BAG_TO_LIST qs) = LIST_TO_BAG (ys1 ++ ys2)`
  by metis_tac[PERM_LIST_TO_BAG]
  \\ gs[LIST_TO_BAG_APPEND, BAG_TO_LIST_INV]
QED

Theorem poly_deg_mult_nonzero_id:
  IntegralDomain r ==>
  !p q. poly p /\ poly q /\ p <> |0| /\ q <> |0|
  ==> Deg r (p * q) = Deg r p + Deg r q
Proof
  strip_tac
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ rpt strip_tac
  \\ irule weak_deg_mult_nonzero
  \\ imp_res_tac poly_lead_eq_zero
  \\ fs[IntegralDomain_def]
QED

Theorem poly_divides_deg_le_id:
  IntegralDomain r ==>
  !p q. poly p /\ poly q /\ q <> |0| /\ p pdivides q ==> Deg r p <= Deg r q
Proof
  strip_tac
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ rpt strip_tac
  \\ `?t. poly t /\ q = t * p` by metis_tac[poly_divides_def]
  \\ `t <> |0|` by metis_tac[poly_mult_lzero]
  \\ `p <> |0|` by metis_tac[poly_mult_rzero]
  \\ rw[poly_deg_mult_nonzero_id]
QED

Definition UniqueFactorizationDomain_def:
  UniqueFactorizationDomain r <=>
    IntegralDomain r /\
    !x. x IN r.carrier /\ x <> r.sum.id ==>
      ?u ps. Unit r u /\ FINITE_BAG ps /\
      BAG_EVERY (\p. ring_prime r p /\ p <> r.sum.id /\ ~Unit r p) ps /\
      SET_OF_BAG ps SUBSET r.carrier /\
      x = r.prod.op u (GBAG r.prod ps)
End

Theorem UniqueFactorizationDomain_Reals[simp]:
  UniqueFactorizationDomain Reals
Proof
  rw[UniqueFactorizationDomain_def]
  \\ qexists_tac`x`
  \\ qexists_tac`{||}`
  \\ simp[] \\ fs[Reals_def]
QED

Theorem UniqueFactorizationDomain_RingIso:
  UniqueFactorizationDomain r /\ Ring s /\ RingIso f r s ==>
  UniqueFactorizationDomain s
Proof
  simp[UniqueFactorizationDomain_def]
  \\ strip_tac
  \\ imp_res_tac integral_domain_ring_iso
  \\ simp[]
  \\ rpt strip_tac
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ drule_then (drule_then drule) ring_iso_sym
  \\ strip_tac
  \\ qmatch_asmsub_abbrev_tac`RingIso g s r`
  \\ first_x_assum(qspec_then`g x`mp_tac)
  \\ `BIJ g s.carrier r.carrier` by fs[RingIso_def]
  \\ impl_keep_tac
  >- (
    conj_tac >- metis_tac[BIJ_DEF, INJ_DEF]
    \\ metis_tac[ring_iso_eq_zero] )
  \\ strip_tac
  \\ qexists_tac`f u`
  \\ qexists_tac`BAG_IMAGE f ps`
  \\ conj_asm1_tac >- metis_tac[ring_iso_unit]
  \\ conj_asm1_tac >- metis_tac[BAG_IMAGE_FINITE]
  \\ conj_asm1_tac
  >- (
    simp[BAG_EVERY, PULL_EXISTS]
    \\ ntac 2 strip_tac
    \\ conj_tac
    >- (
      irule ring_prime_iso
      \\ fs[SUBSET_DEF, BAG_EVERY]
      \\ metis_tac[] )
    \\ conj_tac
    >- (
      fs[BAG_EVERY, SUBSET_DEF]
      \\ metis_tac[ring_iso_eq_zero] )
    \\ fs[BAG_EVERY, SUBSET_DEF]
    \\ strip_tac
    \\ `y = g (f y)` by metis_tac[helperSetTheory.BIJ_LINV_THM, RingIso_def]
    \\ metis_tac[ring_iso_unit])
  \\ conj_asm1_tac
  >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[BIJ_DEF, INJ_DEF, RingIso_def] )
  \\ DEP_REWRITE_TAC[Q.SPEC`r.prod`(GSYM (Q.GEN`g`MonoidHomo_GBAG))]
  \\ conj_asm1_tac
  >- ( simp[] \\ metis_tac[RingIso_def, RingHomo_def, Ring_def] )
  \\ `GBAG r.prod ps IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ fs[] )
  \\ fs[MonoidHomo_def]
  \\ `u IN r.prod.carrier`
  by metis_tac[ringUnitTheory.ring_unit_property, ring_carriers]
  \\ `f (g x) = x` suffices_by metis_tac[]
  \\ metis_tac[helperSetTheory.BIJ_LINV_THM, RingIso_def]
QED

Definition ring_is_gcd_def:
  ring_is_gcd r p q g <=>
    g IN r.carrier /\
    ring_divides r g p /\
    ring_divides r g q /\
    !d. d IN r.carrier /\
        ring_divides r d p /\
        ring_divides r d q ==>
        ring_divides r d g
End

Theorem EuclideanRing_ring_gcd_is_gcd:
  EuclideanRing r f ==> !p q. p IN r.carrier /\ q IN r.carrier ==>
    ring_is_gcd r p q (ring_gcd r f p q)
Proof
  rpt strip_tac
  \\ drule ring_gcd_property
  \\ rw[ring_is_gcd_def]
  >- metis_tac[ring_gcd_element]
  >- metis_tac[ring_gcd_divides]
  >- metis_tac[ring_gcd_divides]
QED

Definition GCDDomain_def:
  GCDDomain r <=> IntegralDomain r /\
    !p q. p IN ring_nonzero r /\ q IN ring_nonzero r
          ==> ?g. ring_is_gcd r p q g
End

Theorem ring_is_gcd_zero:
  Ring r /\ ring_is_gcd r p q g /\ p IN R /\ q IN R ==>
  (g = #0 <=> p = #0 /\ q = #0)
Proof
  rw[ring_is_gcd_def]
  \\ eq_tac >- metis_tac[ring_zero_divides]
  \\ rw[]
  \\ first_x_assum(qspec_then`#0`mp_tac)
  \\ simp[ring_zero_divides]
QED

Theorem GCDDomain_irreducible_prime:
  GCDDomain r ==> !p. irreducible r p ==> ring_prime r p
Proof
  rw[GCDDomain_def, ring_prime_def]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ Cases_on`a = #0` \\ gs[]
  \\ Cases_on`b = #0` \\ gs[]
  \\ `p IN R /\ p <> #0` by fs[irreducible_def, ring_nonzero_eq]
  \\ `p * b <> #0` by metis_tac[IntegralDomain_def]
  \\ `a * b <> #0` by metis_tac[IntegralDomain_def]
  \\ `∃g. ring_is_gcd r (p * b) (a * b) g`
  by metis_tac[ring_nonzero_eq, ring_mult_element]
  \\ `g <> #0` by metis_tac[ring_is_gcd_zero, ring_mult_element]
  \\ `ring_divides r g (p * b) /\ ring_divides r g (a * b)`
  by metis_tac[ring_is_gcd_def]
  \\ `p rdivides p * b` by metis_tac[ring_divides_def, ring_mult_comm]
  \\ `b rdivides p * b` by metis_tac[ring_divides_def]
  \\ `b rdivides a * b` by metis_tac[ring_divides_def]
  \\ `p rdivides g /\ b rdivides g` by metis_tac[ring_is_gcd_def]
  \\ `?s. s IN R /\ g = s * b` by metis_tac[ring_divides_def]
  \\ `s rdivides p`
  by (
    rw[]
    \\ fs[ring_divides_def]
    \\ qmatch_asmsub_rename_tac`p * b = z * b`
    \\ `p = z` by metis_tac[integral_domain_mult_rcancel]
    \\ qmatch_assum_rename_tac`p * b = x * (y * b)`
    \\ `x * y IN R` by metis_tac[ring_mult_element]
    \\ `x * (y * b) = x * y * b` by metis_tac[ring_mult_assoc]
    \\ `x * y = z` by metis_tac[integral_domain_mult_rcancel]
    \\ metis_tac[] )
  \\ `∃t. t IN R /\ p = t * s` by metis_tac[ring_divides_def]
  \\ Cases_on`unit s`
  >- (
    rw[]
    \\ disj2_tac
    \\ qpat_x_assum`t * s rdivides _`mp_tac
    \\ simp[ring_divides_def]
    \\ disch_then(qx_choose_then`z`strip_assume_tac)
    \\ qexists_tac`|/ s * z`
    \\ simp[ring_unit_inv_element]
    \\ `|/ s * (s * b) = |/ s * (z * (t * s))` by metis_tac[]
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ conj_tac >- simp[ring_unit_inv_element]
    \\ simp[ring_unit_linv] )
  \\ `unit t` by metis_tac[irreducible_def]
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ qpat_x_assum`x rdivides _ * x`kall_tac
  \\ qpat_x_assum`x rdivides _ * x`kall_tac
  \\ qpat_x_assum`x rdivides _ * x`kall_tac
  \\ qpat_x_assum`x rdivides _ * x`kall_tac
  \\ qpat_x_assum`x * y rdivides x * y * _`kall_tac
  \\ qpat_x_assum`x * y rdivides _ * x * y`kall_tac
  \\ `∃c. c IN R /\ a * b = c * (s * b)` by metis_tac[ring_divides_def]
  \\ `a * b = c * s * b` by simp[ring_mult_assoc]
  \\ `c * s IN R` by simp[]
  \\ `a = c * s` by metis_tac[integral_domain_mult_rcancel]
  \\ simp[ring_divides_def]
  \\ disj1_tac
  \\ qexists_tac`c * |/ t`
  \\ simp[ring_unit_inv_element]
  \\ simp[ring_mult_assoc, ring_unit_inv_element]
  \\ AP_TERM_TAC
  \\ simp[GSYM ring_mult_assoc, ring_unit_inv_element]
  \\ simp[ring_unit_linv]
QED

Theorem UniqueFactorizationDomain_irreducible_prime:
  !r. UniqueFactorizationDomain r ==> !p. irreducible r p ==> ring_prime r p
Proof
  rw[ring_prime_def]
  \\ spose_not_then strip_assume_tac
  \\ `p IN r.carrier /\ p <> r.sum.id`
  by metis_tac[irreducible_def, ring_nonzero_def, IN_DIFF, IN_SING]
  \\ `IntegralDomain r` by metis_tac[UniqueFactorizationDomain_def]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ fs[UniqueFactorizationDomain_def]
  \\ `a <> #0` by metis_tac[ring_divides_zero]
  \\ `b <> #0` by metis_tac[ring_divides_zero]
  \\ last_assum(qspec_then`a`mp_tac)
  \\ last_assum(qspec_then`b`mp_tac)
  \\ impl_tac >- simp[]
  \\ disch_then(qx_choosel_then[`bu`,`bps`]strip_assume_tac)
  \\ impl_tac >- simp[]
  \\ disch_then(qx_choosel_then[`au`,`aps`]strip_assume_tac)
  \\ `GBAG r.prod aps IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[] \\ metis_tac[Ring_def] )
  \\ `GBAG r.prod bps IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[] \\ metis_tac[Ring_def] )
  \\ `unit (au * bu)` by metis_tac[ringUnitTheory.ring_unit_mult_unit]
  \\ `a * b = (au * bu) * (GBAG r.prod (BAG_UNION aps bps))`
  by (
    DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ conj_tac >- metis_tac[Ring_def]
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ rfs[]
    \\ AP_TERM_TAC
    \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ simp[]
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ rfs[]
    \\ AP_TERM_TAC
    \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ simp[] )
  \\ first_assum(qspec_then`p`mp_tac)
  \\ impl_tac >- simp[]
  \\ disch_then(qx_choosel_then[`pu`,`pps`]strip_assume_tac)
  \\ `∃s. a * b = s * p /\ s IN R` by metis_tac[ring_divides_def]
  \\ `s <> #0` by metis_tac[ring_mult_lzero, IntegralDomain_def]
  \\ first_assum(qspec_then`s`mp_tac)
  \\ impl_tac >- simp[]
  \\ disch_then(qx_choosel_then[`su`,`sps`]strip_assume_tac)
  \\ `GBAG r.prod sps IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[] \\ metis_tac[Ring_def] )
  \\ `GBAG r.prod pps IN r.prod.carrier`
  by ( irule GBAG_in_carrier \\ simp[] \\ metis_tac[Ring_def] )
  \\ `unit (su * pu)` by metis_tac[ringUnitTheory.ring_unit_mult_unit]
  \\ `s * p = (su * pu) * (GBAG r.prod (BAG_UNION sps pps))`
  by (
    DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[]
    \\ conj_tac >- metis_tac[Ring_def]
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ rfs[]
    \\ AP_TERM_TAC
    \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ simp[]
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ rfs[]
    \\ AP_TERM_TAC
    \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm] \\ simp[] )
  \\ `ring_associates r (GBAG r.prod (BAG_UNION aps bps))
                        (GBAG r.prod (BAG_UNION sps pps))`
  by (
    simp[ring_associates_def]
    \\ qexists_tac`|/ (au * bu) * (su * pu)`
    \\ qmatch_goalsub_abbrev_tac`|/ x`
    \\ conj_tac >- (
      irule ring_unit_mult_unit
      \\ simp[] \\ irule ring_unit_has_inv
      \\ simp[] )
    \\ DEP_ONCE_REWRITE_TAC[ring_mult_assoc]
    \\ conj_asm1_tac
    >- (
      simp[]
      \\ simp[ring_unit_inv_element]
      \\ DEP_REWRITE_TAC[GBAG_UNION]
      \\ simp[]
      \\ rfs[]
      \\ metis_tac[Ring_def] )
    \\ first_x_assum (CHANGED_TAC o SUBST1_TAC o SYM)
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC)
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ conj_asm1_tac
    >- (
      simp[]
      \\ DEP_REWRITE_TAC[GBAG_UNION]
      \\ simp[] \\ rfs[]
      \\ metis_tac[Ring_def] )
    \\ DEP_REWRITE_TAC[ring_unit_linv]
    \\ simp[ring_mult_lone] )
  \\ drule integral_domain_prime_factors_unique
  \\ disch_then(qspec_then`BAG_TO_LIST (BAG_UNION aps bps)`mp_tac)
  \\ disch_then(qspec_then`BAG_TO_LIST (BAG_UNION sps pps)`mp_tac)
  \\ simp[BAG_TO_LIST_INV]
  \\ fs[BAG_EVERY]
  \\ dsimp[]
  \\ fs[SUBSET_DEF]
  \\ spose_not_then strip_assume_tac
  \\ qpat_x_assum`~(_ rdivides _)`mp_tac
  \\ qpat_x_assum`~(_ rdivides _)`mp_tac
  \\ simp[ring_divides_def]
  \\ Cases_on`pps`
  >- ( fs[] \\ metis_tac[irreducible_def] )
  \\ reverse(Cases_on`b0`)
  >- (
    fs[]
    \\ qpat_x_assum`irreducible r _`mp_tac
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ simp[]
    \\ fs[SUBSET_DEF]
    \\ rfs[]
    \\ conj_tac >- metis_tac[Ring_def]
    \\ simp[irreducible_def]
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`pu * (e * (e' * xx))`
    \\ `xx IN r.prod.carrier`
    by (
      qunabbrev_tac`xx`
      \\ irule GBAG_in_carrier
      \\ simp[SUBSET_DEF]
      \\ metis_tac[Ring_def] )
    \\ `e IN r.carrier /\ e' IN r.carrier` by metis_tac[]
    \\ `~unit e /\ ~unit e'` by metis_tac[]
    \\ `pu * (e * (e' * xx)) = e * (e' * (pu * xx))`
    by (
      DEP_ONCE_REWRITE_TAC[ring_mult_comm]
      \\ simp[] \\ rfs[]
      \\ DEP_REWRITE_TAC[ring_mult_assoc]
      \\ simp[]
      \\ AP_TERM_TAC
      \\ AP_TERM_TAC
      \\ DEP_ONCE_REWRITE_TAC[ring_mult_comm]
      \\ simp[] )
    \\ `e' * (pu * xx) IN r.carrier` by rfs[]
    \\ `unit (e' * (pu * xx))` by metis_tac[]
    \\ `pu * xx IN R` by rfs[]
    \\ metis_tac[ring_unit_mult_eq_unit] )
  \\ fs[]
  \\ `MEM e l3`
  by (
    imp_res_tac MEM_PERM
    \\ rfs[MEM_BAG_TO_LIST]
    \\ metis_tac[] )
  \\ fs[LIST_REL_EL_EQN]
  \\ fs[MEM_EL]
  \\ first_x_assum(qspec_then`n`mp_tac)
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`rassoc ab _`
  \\ `MEM ab (BAG_TO_LIST (BAG_UNION aps bps))` by metis_tac[MEM_EL]
  \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`rassoc ab e`
  \\ rfs[]
  >- (
    `F` suffices_by rw[]
    \\ qpat_x_assum`!s. _`mp_tac
    \\ simp[]
    \\ `aps = BAG_INSERT ab (aps - {|ab|})`
    by (
      simp[BAG_EXTENSION, BAG_INN, BAG_INSERT, BAG_DIFF, EMPTY_BAG]
      \\ fs[BAG_IN, BAG_INN] \\ rw[] )
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ simp[FINITE_BAG_DIFF, SUBSET_DEF]
    \\ conj_tac >- metis_tac[BAG_IN_DIFF_E, Ring_def]
    \\ qmatch_goalsub_abbrev_tac`ab * rr`
    \\ qpat_x_assum`ring_associates _ _ _`mp_tac
    \\ simp[ring_associates_def]
    \\ strip_tac
    \\ qexists_tac`au * s * rr * |/ pu`
    \\ `s IN R` by metis_tac[ring_unit_property]
    \\ `|/ pu IN R` by metis_tac[ring_unit_inv_element]
    \\ `rr IN r.prod.carrier`
    by (
      qunabbrev_tac`rr`
      \\ irule GBAG_in_carrier
      \\ fs[SUBSET_DEF, FINITE_BAG_DIFF]
      \\ metis_tac[BAG_IN_DIFF_E, Ring_def] )
    \\ rfs[]
    \\ DEP_REWRITE_TAC[ring_mult_assoc]
    \\ simp[]
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ simp[Once ring_mult_comm]
    \\ AP_TERM_TAC
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ simp[]
    \\ DEP_REWRITE_TAC[ring_unit_linv]
    \\ simp[] )
  \\ `bps = BAG_INSERT ab (bps - {|ab|})`
  by (
    simp[BAG_EXTENSION, BAG_INN, BAG_INSERT, BAG_DIFF, EMPTY_BAG]
    \\ fs[BAG_IN, BAG_INN] \\ rw[] )
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[FINITE_BAG_DIFF, SUBSET_DEF]
  \\ conj_tac >- metis_tac[BAG_IN_DIFF_E, Ring_def]
  \\ qmatch_goalsub_abbrev_tac`ab * rr`
  \\ qpat_x_assum`ring_associates _ _ _`mp_tac
  \\ simp[ring_associates_def]
  \\ strip_tac
  \\ qexists_tac`bu * s * rr * |/ pu`
  \\ `s IN R` by metis_tac[ring_unit_property]
  \\ `|/ pu IN R` by metis_tac[ring_unit_inv_element]
  \\ `rr IN r.prod.carrier`
  by (
    qunabbrev_tac`rr`
    \\ irule GBAG_in_carrier
    \\ fs[SUBSET_DEF, FINITE_BAG_DIFF]
    \\ metis_tac[BAG_IN_DIFF_E, Ring_def] )
  \\ rfs[]
  \\ DEP_REWRITE_TAC[ring_mult_assoc]
  \\ simp[]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[Once ring_mult_comm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
  \\ simp[]
  \\ DEP_REWRITE_TAC[ring_unit_linv]
  \\ simp[]
QED

Definition ascending_chain_condition_principal_ideals_def:
  ascending_chain_condition_principal_ideals r <=>
    !f. (!n. f n IN r.carrier) /\
        (!n. (coset r.prod (f n) r.carrier) SUBSET
             (coset r.prod (f (SUC n)) r.carrier))
        ==> ?m. !n. m < n ==> (coset r.prod (f n) r.carrier) =
                              (coset r.prod (f m) r.carrier)
End

Theorem accp_alt:
  ascending_chain_condition_principal_ideals r <=>
  ~?f. (!n. f n IN r.carrier) /\
       (!n. (coset r.prod (f n) r.carrier) PSUBSET
            (coset r.prod (f (SUC n)) r.carrier))
Proof
  rw[ascending_chain_condition_principal_ideals_def]
  \\ rw[EQ_IMP_THM]
  >- (
    CCONTR_TAC \\ fs[]
    \\ first_x_assum(qspec_then`f`mp_tac)
    \\ simp[]
    \\ fs[PSUBSET_DEF]
    \\ gen_tac
    \\ qexists_tac`SUC m`
    \\ simp[]
    \\ metis_tac[] )
  \\ spose_not_then strip_assume_tac
  \\ last_x_assum mp_tac
  \\ simp[]
  \\ fs[SKOLEM_THM]
  \\ qexists_tac`λn. f (FUNPOW f' n 0)`
  \\ simp[arithmeticTheory.FUNPOW_SUC]
  \\ rw[PSUBSET_DEF]
  \\ qmatch_goalsub_abbrev_tac`f m`
  \\ `m < f' m` by metis_tac[]
  \\ qpat_x_assum`Abbrev _`kall_tac
  \\ qmatch_asmsub_rename_tac`m < n`
  \\ completeInduct_on`n - m` \\ simp[]
  \\ Cases \\ simp[]
  \\ rw[]
  \\ qmatch_asmsub_rename_tac`m < SUC n`
  \\ irule SUBSET_TRANS
  \\ qexists_tac`f n * R`
  \\ reverse conj_tac >- metis_tac[]
  \\ Cases_on`m = n` \\ simp[]
QED

Definition AtomicDomain_def:
  AtomicDomain r <=> IntegralDomain r /\
  (!x. x IN r.carrier /\ x <> r.sum.id /\ ~Unit r x ==>
       ?qs. FINITE_BAG qs /\ BAG_EVERY (irreducible r) qs /\
            x = GBAG r.prod qs)
End

Theorem accp_atomic:
  IntegralDomain r /\
  ascending_chain_condition_principal_ideals r
  ==>
  AtomicDomain r
Proof
  rw[AtomicDomain_def, ascending_chain_condition_principal_ideals_def]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ spose_not_then strip_assume_tac
  \\ Cases_on`irreducible r x`
  >- (
    first_x_assum(qspec_then`{|x|}`mp_tac)
    \\ simp[]
    \\ metis_tac[ring_mult_rone, IntegralDomain_def] )
  \\ `∀x. irreducible r x ==> x IN r.carrier`
  by metis_tac[irreducible_def, IN_DIFF, ring_nonzero_def]
  \\ `AbelianMonoid r.prod` by metis_tac[Ring_def]
  \\ `∀z. ?y.
        z IN r.carrier /\ z <> r.sum.id /\ ~Unit r z /\ ~irreducible r z /\
        (!qs. FINITE_BAG qs /\ BAG_EVERY (irreducible r) qs ==>
              z <> GBAG r.prod qs) ==>
        y IN r.carrier /\
        ring_divides r y z /\ ¬ring_associates r y z /\
        ~Unit r y /\ ~irreducible r y /\
        y <> r.sum.id /\
        (!qs. FINITE_BAG qs /\ BAG_EVERY (irreducible r) qs ==>
              y <> GBAG r.prod qs)`
  by (
    rpt strip_tac
    \\ simp[RIGHT_EXISTS_IMP_THM]
    \\ strip_tac
    \\ `∃a b. a IN r.carrier /\ b IN r.carrier /\ z = r.prod.op a b /\
              ~Unit r a /\ ~Unit r b` by (
      qpat_x_assum`~irreducible r z`mp_tac
      \\ simp[irreducible_def, ring_nonzero_def, PULL_EXISTS]
      \\ metis_tac[] )
    \\ Cases_on`∃qa qb. FINITE_BAG qa /\ FINITE_BAG qb /\
                        BAG_EVERY atom qa /\ BAG_EVERY atom qb /\
                        a = GBAG r.prod qa /\ b = GBAG r.prod qb`
    >- (
      pop_assum strip_assume_tac
      \\ first_x_assum(qspec_then`BAG_UNION qa qb`mp_tac)
      \\ impl_tac >- simp[]
      \\ DEP_REWRITE_TAC[GBAG_UNION]
      \\ simp[SUBSET_DEF]
      \\ metis_tac[BAG_EVERY] )
    \\ Cases_on`∃qa. FINITE_BAG qa /\ BAG_EVERY atom qa /\ a = GBAG r.prod qa`
    >- (
      pop_assum strip_assume_tac
      \\ qexists_tac`b`
      \\ simp[]
      \\ conj_tac >- metis_tac[ring_divides_def]
      \\ reverse conj_asm2_tac
      >- (
        conj_tac
        >- (
          strip_tac
          \\ first_x_assum(qspec_then`BAG_INSERT b qa`mp_tac)
          \\ simp[]
          \\ DEP_REWRITE_TAC[GBAG_INSERT]
          \\ simp[SUBSET_DEF]
          \\ metis_tac[ring_mult_comm, BAG_EVERY])
        \\ conj_tac >- metis_tac[IntegralDomain_def]
        \\ metis_tac[] )
      \\ qpat_x_assum`a = _`(assume_tac o SYM) \\ simp[]
      \\ qpat_x_assum`z = _`(assume_tac o SYM) \\ simp[]
      \\ simp[ring_associates_def, ring_unit_property]
      \\ rpt strip_tac
      \\ Cases_on`s IN R` \\ simp[]
      \\ rpt strip_tac
      \\ `(a * s) * z = #1 * z` by metis_tac[ring_mult_assoc, ring_mult_lone]
      \\ `a * s IN R /\ #1 IN R` by simp[]
      \\ `a * s = #1` by metis_tac[integral_domain_mult_rcancel]
      \\ `Unit r a` by metis_tac[ring_unit_property])
    \\ qexists_tac`a`
    \\ simp[]
    \\ conj_tac >- metis_tac[ring_divides_def, ring_mult_comm]
    \\ reverse conj_asm2_tac
    >- (
      conj_tac
      >- (
        strip_tac
        \\ `a = GBAG r.prod {|a|}` by simp[]
        \\ `BAG_EVERY atom {|a|}` by simp[]
        \\ `FINITE_BAG {|a|}` by simp[]
        \\ metis_tac[] )
      \\ metis_tac[IntegralDomain_def])
    \\ qpat_x_assum`z = _`(assume_tac o SYM) \\ simp[]
    \\ simp[ring_associates_def, ring_unit_property]
    \\ rpt strip_tac
    \\ Cases_on`s IN R` \\ simp[]
    \\ rpt strip_tac
    \\ `z * (s * b) = z * #1`
    by metis_tac[ring_mult_assoc, ring_mult_comm, ring_mult_rone]
    \\ `s * b IN R /\ #1 IN R` by simp[]
    \\ `s * b = #1` by metis_tac[integral_domain_mult_lcancel]
    \\ `Unit r b` by metis_tac[ring_unit_property, ring_mult_comm] )
  \\ fs[SKOLEM_THM]
  \\ qabbrev_tac`g = PRIM_REC x (\x n. f x)`
  \\ `∀n. g n IN r.carrier /\ g n <> #0 /\ ~Unit r (g n) /\ ~irreducible r (g n)
          /\ (!qs. FINITE_BAG qs /\ BAG_EVERY atom qs ==> g n <> GBAG r.prod qs) /\ (g (SUC n) rdivides (g n)) /\ ~rassoc (g (SUC n)) (g n)`
  by (
    Induct
    >- simp[Abbr`g`, prim_recTheory.PRIM_REC_THM]
    \\ `f (g n) = g (SUC n)`
    by simp[Abbr`g`, prim_recTheory.PRIM_REC_THM]
    \\ conj_asm1_tac >- metis_tac[]
    \\ conj_asm1_tac >- metis_tac[]
    \\ conj_asm1_tac >- metis_tac[]
    \\ conj_asm1_tac >- metis_tac[]
    \\ conj_asm1_tac >- metis_tac[]
    \\ `f (g (SUC n)) = g (SUC (SUC n))`
    by (
      qunabbrev_tac`g`
      \\ simp[Once prim_recTheory.PRIM_REC_THM, SimpRHS] )
    \\ metis_tac[])
  \\ first_x_assum(qspec_then`g`mp_tac)
  \\ impl_tac
  >- (
    conj_tac >- metis_tac[]
    \\ simp[SUBSET_DEF, subgroupTheory.in_coset, PULL_EXISTS]
    \\ rpt strip_tac
    \\ `g (SUC n) rdivides g n` by metis_tac[]
    \\ `∃s. s IN R /\ g n = s * g (SUC n)` by metis_tac[ring_divides_def]
    \\ qexists_tac`s * y`
    \\ `g n IN R /\ g (SUC n) IN R` by metis_tac[]
    \\ simp[GSYM ring_mult_assoc]
    \\ simp[ring_mult_comm] )
  \\ simp[]
  \\ gen_tac
  \\ qexists_tac`SUC m`
  \\ simp[]
  \\ `∃s. s IN R /\ g m = s * g (SUC m) /\ ~Unit r s`
  by metis_tac[ring_divides_def, ring_associates_def,
               ring_mult_comm, ring_associates_sym]
  \\ simp[subgroupTheory.coset_alt]
  \\ simp[Once EXTENSION]
  \\ spose_not_then strip_assume_tac
  \\ first_x_assum(qspec_then`g (SUC m)`mp_tac)
  \\ qmatch_goalsub_abbrev_tac`a <=> _`
  \\ `a = T` by ( simp[Abbr`a`] \\ qexists_tac`#1` \\ simp[] )
  \\ simp[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ rpt strip_tac
  \\ `#1 IN R` by simp[]
  \\ `s * z IN R` by simp[]
  \\ `#1 * g (SUC m) = s * z * g (SUC m)`
  by metis_tac[ring_mult_lone, ring_mult_assoc, ring_mult_comm]
  \\ `s * z = #1` by metis_tac[integral_domain_mult_rcancel]
  \\ metis_tac[ring_unit_property]
QED

Theorem ufd_accp:
  UniqueFactorizationDomain r ==>
  ascending_chain_condition_principal_ideals r
Proof
  rw[UniqueFactorizationDomain_def, accp_alt]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ spose_not_then strip_assume_tac
  \\ `∃n0. f n0 <> #0`
  by (
    spose_not_then strip_assume_tac
    \\ `#0 * R PSUBSET #0 * R` by metis_tac[]
    \\ fs[] )
  \\ first_assum(qspec_then`f n0`mp_tac)
  \\ impl_tac >- simp[] \\ strip_tac
  \\ `∀m. n0 < m ==> f n0 * R PSUBSET f m * R`
  by (
    Induct \\ simp[]
    \\ Cases_on`n0 = m`
    >- ( simp[] \\ metis_tac[] )
    \\ strip_tac \\ fs[]
    \\ metis_tac[PSUBSET_TRANS] )
  \\ `!n x. x IN f n * R <=> f n rdivides x`
  by (
    rpt strip_tac
    \\ `f n * R = (principal_ideal r (f n)).carrier`
    by simp[principal_ideal_property]
    \\ metis_tac[principal_ideal_element_divides, IntegralDomain_def] )
  \\ `∀m x. n0 < m /\ f n0 rdivides x ==> f m rdivides x`
  by metis_tac[PSUBSET_DEF, SUBSET_DEF]
  \\ `∀m. n0 < m ==> ?qs. qs <= ps /\ rassoc (f m) (GBAG r.prod qs)`
  by (
    rpt strip_tac
    \\ spose_not_then strip_assume_tac
    \\ `GBAG r.prod ps IN r.carrier` by rfs[]
    \\ `f n0 rdivides (GBAG r.prod ps)`
    by (
      simp[ring_divides_def]
      \\ qpat_x_assum`unit u`mp_tac
      \\ simp[ring_unit_property] \\ strip_tac
      \\ qexists_tac`v`
      \\ simp[GSYM ring_mult_assoc]
      \\ metis_tac[ring_mult_comm, ring_mult_lone] )
    \\ `f m rdivides (GBAG r.prod ps)` by metis_tac[]
    \\ pop_assum mp_tac
    \\ simp_tac std_ss [ring_divides_def]
    \\ rpt strip_tac
    \\ `GBAG r.prod ps <> #0` by (strip_tac \\ gs[])
    \\ `s <> #0 /\ f m <> #0` by (rpt strip_tac \\ gs[])
    \\ last_assum(qspec_then`s`mp_tac)
    \\ impl_tac >- simp[]
    \\ disch_then(qx_choosel_then[`su`,`sps`]strip_assume_tac)
    \\ last_assum(qspec_then`f m`mp_tac)
    \\ impl_tac >- simp[]
    \\ disch_then(qx_choosel_then[`fu`,`fps`]strip_assume_tac)
    \\ `su IN R /\ fu IN R` by metis_tac[ring_unit_property]
    \\ `AbelianMonoid r.prod` by metis_tac[Ring_def]
    \\ `GBAG r.prod sps IN r.prod.carrier /\ GBAG r.prod fps IN r.prod.carrier`
    by (conj_tac \\ irule GBAG_in_carrier \\ simp[])
    \\ `r.prod.carrier = r.carrier` by simp[]
    \\ `GBAG r.prod ps = (su * fu) * (GBAG r.prod sps * GBAG r.prod fps)`
    by (
      fs[]
      \\ simp[ring_mult_assoc]
      \\ AP_TERM_TAC
      \\ simp[Once ring_mult_comm]
      \\ simp[ring_mult_assoc]
      \\ AP_TERM_TAC
      \\ simp[Once ring_mult_comm] )
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[GSYM GBAG_UNION]
    \\ conj_tac >- simp[] \\ strip_tac
    \\ `rassoc (GBAG r.prod (LIST_TO_BAG (BAG_TO_LIST ps)))
               (GBAG r.prod (LIST_TO_BAG (BAG_TO_LIST (BAG_UNION sps fps))))`
    by (
      rewrite_tac[ring_associates_def]
      \\ qexists_tac`su * fu`
      \\ DEP_REWRITE_TAC[BAG_TO_LIST_INV]
      \\ conj_tac >- simp[]
      \\ conj_tac >- metis_tac[ring_unit_mult_unit]
      \\ simp[] )
    \\ drule integral_domain_prime_factors_unique
    \\ disch_then(first_assum o mp_then Any mp_tac)
    \\ impl_tac
    >- (
      simp[]
      \\ fs[BAG_EVERY, SUBSET_DEF]
      \\ metis_tac[] )
    \\ strip_tac
    \\ `PERM l3 (BAG_TO_LIST sps ++ BAG_TO_LIST fps)`
    by metis_tac[PERM_BAG_TO_LIST_UNION_APPEND, PERM_TRANS, PERM_SYM]
    \\ drule LIST_REL_PERM
    \\ disch_then drule
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`LIST_REL _ l4 (l1 ++ l2)`
    \\ `l4 = TAKE (LENGTH l1) l4 ++ DROP (LENGTH l1) l4`
    by metis_tac[TAKE_DROP]
    \\ imp_res_tac LIST_REL_LENGTH
    \\ `LENGTH (TAKE (LENGTH l1) l4) = LENGTH l1` by simp[]
    \\ `LIST_REL rassoc (DROP (LENGTH l1) l4) l2`
    by metis_tac[LIST_REL_APPEND_IMP]
    \\ first_x_assum(qspec_then`LIST_TO_BAG (DROP (LENGTH l1)l4)`mp_tac)
    \\ simp_tac(srw_ss())[]
    \\ conj_tac
    >- (
      `ps = LIST_TO_BAG (BAG_TO_LIST ps)` by simp[BAG_TO_LIST_INV]
      \\ pop_assum SUBST1_TAC
      \\ `LIST_TO_BAG (BAG_TO_LIST ps) = LIST_TO_BAG l4`
      by metis_tac[PERM_LIST_TO_BAG]
      \\ pop_assum SUBST1_TAC
      \\ qmatch_goalsub_abbrev_tac`LIST_TO_BAG ll <= _`
      \\ qpat_x_assum`l4 = _`SUBST1_TAC
      \\ qunabbrev_tac`ll`
      \\ rewrite_tac[LIST_TO_BAG_APPEND]
      \\ metis_tac[SUB_BAG_UNION_MONO] )
    \\ irule ring_associates_trans
    \\ conj_tac >- simp[]
    \\ conj_asm1_tac
    >- (
      qpat_x_assum`_ = r.carrier`(SUBST1_TAC o SYM)
      \\ irule GBAG_in_carrier
      \\ simp[SUBSET_DEF, IN_LIST_TO_BAG]
      \\ rpt strip_tac
      \\ drule rich_listTheory.MEM_DROP_IMP
      \\ strip_tac
      \\ `MEM x (BAG_TO_LIST ps)` by metis_tac[MEM_PERM]
      \\ pop_assum mp_tac \\ simp[]
      \\ fs[SUBSET_DEF] )
    \\ qexists_tac`GBAG r.prod fps`
    \\ conj_tac
    >- (
      rewrite_tac[ring_associates_def]
      \\ metis_tac[] )
    \\ `fps = LIST_TO_BAG l2` by simp[Abbr`l2`, BAG_TO_LIST_INV]
    \\ pop_assum SUBST1_TAC
    \\ irule ring_associates_sym
    \\ conj_tac >- simp[]
    \\ conj_tac
    >- ( simp[Abbr`l2`, BAG_TO_LIST_INV] \\ rfs[] )
    \\ irule LIST_REL_ring_associates_product
    \\ simp[]
    \\ simp[Abbr`l2`, SUBSET_DEF]
    \\ fs[SUBSET_DEF])
  \\ pop_assum mp_tac
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]))
  \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[SKOLEM_THM]))
  \\ disch_then(qx_choose_then`qs`strip_assume_tac)
  \\ `∀m. n0 < m ==>
          (GBAG r.prod (qs m)) * R PSUBSET
          (GBAG r.prod (qs (SUC m))) * R`
  by (
    rpt strip_tac
    \\ `f m * R PSUBSET (f (SUC m)) * R` by metis_tac[]
    \\ `∀m. n0 < m ==> GBAG r.prod (qs m) IN r.prod.carrier`
    by (
      rpt strip_tac
      \\ irule GBAG_in_carrier
      \\ simp[]
      \\ conj_tac >- metis_tac[Ring_def]
      \\ res_tac
      \\ conj_tac >- metis_tac[FINITE_SUB_BAG]
      \\ imp_res_tac SUB_BAG_SET
      \\ fs[SUBSET_DEF] )
    \\ `f m * R = GBAG r.prod (qs m) * R`
    by ( irule ring_associates_coset \\ simp[] \\ rfs[] )
    \\ `f (SUC m) * R = GBAG r.prod (qs (SUC m)) * R`
    by ( irule ring_associates_coset \\ simp[] \\ rfs[] )
    \\ fs[] )
  \\ `IMAGE (λm. qs (n0 + SUC m)) UNIV SUBSET { b | b <= ps }`
  by simp[SUBSET_DEF, PULL_EXISTS]
  \\ qmatch_asmsub_abbrev_tac`IMAGE qf`
  \\ `∀n m. m < n ==> GBAG r.prod (qf m) * R PSUBSET GBAG r.prod (qf n) * R`
  by (
    Induct
    \\ simp[]
    \\ rpt strip_tac
    \\ Cases_on`m = n`
    >- (
      simp[Abbr`qf`]
      \\ `n0 + SUC (SUC n) = SUC (n0 + SUC n)` by simp[]
      \\ pop_assum SUBST1_TAC
      \\ first_x_assum irule
      \\ simp[] )
    \\ `m < n` by simp[]
    \\ irule PSUBSET_TRANS
    \\ qexists_tac`GBAG r.prod (qf n) * R`
    \\ simp[]
    \\ simp[Abbr`qf`]
    \\ `n0 + SUC (SUC n) = SUC (n0 + SUC n)` by simp[]
    \\ pop_assum SUBST1_TAC
    \\ first_x_assum irule
    \\ simp[] )
  \\ `∀n m. m < n ==> (qf m) <> (qf n)`
  by ( rpt strip_tac \\ metis_tac[PSUBSET_DEF] )
  \\ `∀n m. qf m = qf n ==> m = n`
  by (
    rpt strip_tac
    \\ Cases_on`m < n` >- metis_tac[]
    \\ Cases_on`n < m` >- metis_tac[]
    \\ simp[] )
  \\ `INFINITE (IMAGE qf UNIV)`
  by ( irule IMAGE_11_INFINITE \\ simp[] )
  \\ `INFINITE {b | b <= ps }` by metis_tac[SUBSET_FINITE]
  \\ metis_tac[FINITE_SUB_BAGS]
QED

Theorem ufd_atomic:
  !r. UniqueFactorizationDomain r ==> AtomicDomain r
Proof
  metis_tac[ufd_accp, accp_atomic, UniqueFactorizationDomain_def]
QED

Theorem atomic_unique_ufd:
  AtomicDomain r ==>
  ((!l1 l2. EVERY (irreducible r) l1 /\
            EVERY (irreducible r) l2 /\
            rassoc (GBAG r.prod (LIST_TO_BAG l1))
                   (GBAG r.prod (LIST_TO_BAG l2)) ==>
            ?l3. PERM l2 l3 /\ LIST_REL (ring_associates r) l1 l3)
   <=> UniqueFactorizationDomain r)
Proof
  strip_tac
  \\ reverse eq_tac
  >- (
    rpt strip_tac
    \\ irule integral_domain_prime_factors_unique
    \\ fs[AtomicDomain_def]
    \\ fs[EVERY_MEM]
    \\ simp[UniqueFactorizationDomain_irreducible_prime]
    \\ fs[irreducible_def, ring_nonzero_eq] )
  \\ rw[UniqueFactorizationDomain_def]
  \\ fs[AtomicDomain_def]
  \\ `Ring r` by fs[IntegralDomain_def]
  \\ Cases_on`Unit r x`
  >- (
    qexists_tac`x`
    \\ qexists_tac`{||}`
    \\ simp[] )
  \\ first_assum drule
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ `BAG_EVERY rprime qs`
  by (
    fs[BAG_EVERY]
    \\ rw[ring_prime_def]
    \\ `e IN R /\ e <> #0 /\ ~unit e` by fs[irreducible_def, ring_nonzero_eq]
    \\ fs[ring_divides_def]
    \\ Cases_on`s = #0`
    >- (
      gs[]
      \\ `a = #0 \/ b = #0` by metis_tac[IntegralDomain_def]
      >| [disj1_tac, disj2_tac]
      \\ qexists_tac`#0`
      \\ simp[] )
    \\ `s * e <> #0` by metis_tac[IntegralDomain_def]
    \\ `a <> #0 /\ b <> #0` by (CCONTR_TAC \\ gs[])
    \\ Cases_on`unit a`
    >- (
      disj2_tac
      \\ qexists_tac`|/ a * s`
      \\ simp[ring_unit_inv_element]
      \\ `|/ a * (a * b) = |/ a * (s * e)` by metis_tac[]
      \\ `|/ a * (a * b) = b`
      by (
        pop_assum kall_tac
        \\ qpat_x_assum`a * b = _`(assume_tac o SYM)
        \\ simp[GSYM ring_mult_assoc, ring_unit_inv_element]
        \\ simp[ring_unit_linv] )
      \\ fs[]
      \\ simp[ring_mult_assoc, ring_unit_inv_element] )
    \\ Cases_on`unit b`
    >- (
      disj1_tac
      \\ qexists_tac`s * |/ b`
      \\ simp[ring_unit_inv_element]
      \\ `a * b * |/ b = s * e * |/ b` by metis_tac[]
      \\ gs[ring_mult_assoc, ring_unit_inv_element, ring_unit_rinv]
      \\ AP_TERM_TAC
      \\ simp[ring_mult_comm, ring_unit_inv_element] )
    \\ Cases_on`unit s`
    >- (
      `|/ s * (a * b) = |/ s * (s * e)` by metis_tac[]
      \\ pop_assum mp_tac
      \\ simp[GSYM ring_mult_assoc, ring_unit_inv_element]
      \\ simp[ring_unit_linv]
      \\ strip_tac
      \\ fs[irreducible_def]
      \\ `|/s * a IN R` by simp[ring_unit_inv_element]
      \\ `Unit r (r.prod.op ( |/ s) a)` by metis_tac[]
      \\ metis_tac[ring_unit_mult_eq_unit, ring_unit_inv_element] )
    \\ last_assum(qspec_then`a`mp_tac)
    \\ impl_tac >- simp[]
    \\ disch_then(qx_choose_then`qa`strip_assume_tac)
    \\ last_assum(qspec_then`b`mp_tac)
    \\ impl_tac >- simp[]
    \\ disch_then(qx_choose_then`qb`strip_assume_tac)
    \\ last_assum(qspec_then`s`mp_tac)
    \\ impl_tac >- simp[]
    \\ disch_then(qx_choose_then`qz`strip_assume_tac)
    \\ first_x_assum(qspecl_then[`BAG_TO_LIST (BAG_UNION qa qb)`,
                                 `BAG_TO_LIST (BAG_UNION qz {|e|})`]mp_tac)
    \\ impl_tac
    >- (
      simp[EVERY_MEM]
      \\ conj_tac >- metis_tac[]
      \\ conj_tac >- metis_tac[]
      \\ simp[BAG_TO_LIST_INV]
      \\ DEP_REWRITE_TAC[GBAG_UNION]
      \\ simp[]
      \\ simp[SUBSET_DEF]
      \\ conj_tac >- (
        fs[irreducible_def, ring_nonzero_eq]
        \\ metis_tac[Ring_def] )
      \\ metis_tac[ring_associates_refl, ring_mult_element] )
    \\ strip_tac
    \\ `PERM l3 (BAG_TO_LIST {|e|} ++ BAG_TO_LIST qz)`
    by (
      irule PERM_TRANS
      \\ qexists_tac`BAG_TO_LIST (BAG_UNION {|e|} qz)`
      \\ conj_tac >- metis_tac[PERM_SYM, COMM_BAG_UNION]
      \\ irule PERM_BAG_TO_LIST_UNION_APPEND
      \\ simp[] )
    \\ fs[]
    \\ pop_assum mp_tac
    \\ simp[Once BAG_TO_LIST_THM]
    \\ simp[Once BAG_TO_LIST_THM]
    \\ strip_tac
    \\ `PERM (e::BAG_TO_LIST qz) l3` by simp[PERM_SYM]
    \\ pop_assum mp_tac
    \\ simp[PERM_CONS_EQ_APPEND]
    \\ strip_tac
    \\ BasicProvers.VAR_EQ_TAC
    \\ qhdtm_x_assum`LIST_REL`mp_tac
    \\ simp[LIST_REL_SPLIT2, PULL_EXISTS]
    \\ rpt strip_tac
    \\ `BAG_IN x (BAG_UNION qa qb)`
    by ( first_assum(mp_tac o Q.AP_TERM`MEM x`) \\ simp[] )
    \\ pop_assum mp_tac \\ simp[]
    \\ `rassoc e x` by metis_tac[ring_associates_sym]
    \\ `∃z. unit z /\ e = z * x` by metis_tac[ring_associates_def]
    \\ BasicProvers.VAR_EQ_TAC
    \\ strip_tac \\ drule BAG_DECOMPOSE \\ strip_tac
    \\ BasicProvers.VAR_EQ_TAC
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ fs[SUBSET_DEF]
    \\ (conj_tac >-
         (fs[irreducible_def, ring_nonzero_eq] \\ metis_tac[Ring_def]))
    >| [disj1_tac, disj2_tac]
    \\ qexists_tac`GBAG r.prod b' * |/ z`
    \\ `GBAG r.prod b' IN r.prod.carrier`
    by (
      irule GBAG_in_carrier
      \\ simp[SUBSET_DEF]
      \\ fs[irreducible_def, ring_nonzero_eq]
      \\ metis_tac[Ring_def] )
    \\ gs[ring_unit_inv_element]
    \\ `x IN R` by fs[irreducible_def, ring_nonzero_eq]
    \\ simp[Once ring_mult_comm]
    \\ simp[ring_mult_assoc, ring_unit_inv_element]
    \\ AP_TERM_TAC
    \\ simp[GSYM ring_mult_assoc, ring_unit_inv_element]
    \\ simp[ring_unit_linv])
  \\ qexists_tac`#1`
  \\ qexists_tac`qs`
  \\ simp[]
  \\ `GBAG r.prod qs IN r.prod.carrier`
  by (
    irule GBAG_in_carrier
    \\ fs[]
    \\ fs[BAG_EVERY, SUBSET_DEF, irreducible_def, ring_nonzero_eq]
    \\ metis_tac[Ring_def] )
  \\ simp[SUBSET_DEF]
  \\ fs[BAG_EVERY]
  \\ fs[irreducible_def, ring_nonzero_eq]
QED

Theorem atomic_irreducible_prime_ufd:
  AtomicDomain r ==>
  ((!x. irreducible r x ==> rprime x) <=>
   UniqueFactorizationDomain r)
Proof
  strip_tac
  \\ reverse eq_tac
  >- metis_tac[UniqueFactorizationDomain_irreducible_prime]
  \\ rw[UniqueFactorizationDomain_def]
  \\ fs[AtomicDomain_def]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ Cases_on`Unit r x`
  >- (
    qexists_tac`x`
    \\ qexists_tac`{||}`
    \\ simp[] )
  \\ first_x_assum(qspec_then`x`drule)
  \\ simp[] \\ strip_tac
  \\ qexists_tac`#1`
  \\ qexists_tac`qs`
  \\ simp[]
  \\ fs[BAG_EVERY, SUBSET_DEF]
  \\ metis_tac[irreducible_def, ring_nonzero_eq]
QED

Theorem PolyRing_accp:
  IntegralDomain r /\ ascending_chain_condition_principal_ideals r ==>
  ascending_chain_condition_principal_ideals (PolyRing r)
Proof
  rw[accp_alt]
  \\ spose_not_then strip_assume_tac
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ Cases_on`∃n. f (SUC n) = |0|`
  >- (
    pop_assum strip_assume_tac
    \\ qspec_then`PolyRing r`mp_tac zero_ideal_sing
    \\ impl_tac >- simp[poly_ring_ring]
    \\ simp[principal_ideal_property]
    \\ strip_tac \\ fs[]
    \\ `coset (PolyRing r).prod (f n) (PolyRing r).carrier PSUBSET {[]}`
    by metis_tac[]
    \\ fs[PSUBSET_SING]
    \\ fs[subgroupTheory.coset_def] )
  \\ `∀n. f (SUC n) pdivides f n`
  by (
    strip_tac
    \\ rewrite_tac[poly_divides_is_ring_divides]
    \\ DEP_REWRITE_TAC[GSYM principal_ideal_element_divides]
    \\ fs[PSUBSET_DEF, poly_ring_ring]
    \\ simp[principal_ideal_property]
    \\ fs[SUBSET_DEF]
    \\ first_x_assum(qspec_then`n`(irule o CONJUNCT1))
    \\ simp[GSYM principal_ideal_property]
    \\ irule principal_ideal_has_element
    \\ simp[poly_ring_ring] )
  \\ `∀n. Deg r (f (SUC (SUC n))) <= Deg r (f (SUC n))`
  by (
    strip_tac
    \\ irule poly_divides_deg_le_id
    \\ fs[poly_ring_element] )
  \\ `∀n m. 0 < n /\ n <= m ==> deg (f m) <= deg (f n)`
  by (
    rpt strip_tac
    \\ completeInduct_on`m - n`
    \\ rpt strip_tac
    \\ Cases_on`n` \\ fs[]
    \\ Cases_on`m` \\ fs[]
    \\ qmatch_asmsub_rename_tac`m <= n`
    \\ Cases_on`m = n` \\ simp[]
    \\ irule arithmeticTheory.LESS_EQ_TRANS
    \\ qexists_tac`deg (f (SUC (SUC m)))`
    \\ simp[] )
  \\ `∃nn. !n. nn <= n ==> f n <> |0| /\ deg (f n) = deg (f nn)`
  by (
    qabbrev_tac`ld = LEAST d. ?n. deg (f (SUC n)) = d`
    \\ `∀n. ld <= deg (f (SUC n))`
    by (
      qunabbrev_tac`ld`
      \\ gen_tac
      \\ numLib.LEAST_ELIM_TAC
      \\ simp[PULL_EXISTS]
      \\ rw[]
      \\ CCONTR_TAC
      \\ fs[arithmeticTheory.NOT_LESS_EQUAL]
      \\ metis_tac[] )
    \\ qexists_tac`SUC (LEAST nn. deg (f (SUC nn)) = ld)`
    \\ rw[]
    >- ( Cases_on`n` \\ fs[] )
    \\ pop_assum mp_tac
    \\ numLib.LEAST_ELIM_TAC
    \\ rw[]
    >- (
      qunabbrev_tac`ld`
      \\ numLib.LEAST_ELIM_TAC
      \\ simp[] )
    \\ Cases_on`n` \\ fs[]
    \\ simp[arithmeticTheory.EQ_LESS_EQ] )
  \\ `∀n. 0 < n ==> lead (f (SUC n)) rdivides lead (f n)`
  by (
    rpt strip_tac
    \\ `f (SUC n) pdivides f n` by metis_tac[]
    \\ `∃p. poly p /\ f n = p * f (SUC n)` by
    metis_tac[poly_divides_def]
    \\ `∃m. n = SUC m` by (Cases_on`n` \\ fs[] \\ metis_tac[])
    \\ `f n <> |0|` by metis_tac[]
    \\ `f (SUC n) <> |0|` by metis_tac[]
    \\ `p <> |0|` by (
      `Ring (PolyRing r)` by simp[poly_ring_ring]
      \\ metis_tac[ring_mult_lzero] )
    \\ `poly (f (SUC n))` by metis_tac[poly_ring_element]
    \\ `lead p <> #0 /\ lead (f (SUC n)) <> #0`
    by metis_tac[poly_lead_eq_zero]
    \\ `lead p IN r.carrier /\ lead (f (SUC n)) IN r.carrier`
    by metis_tac[poly_lead_element]
    \\ `lead p * lead (f (SUC n)) <> #0`
    by metis_tac[IntegralDomain_def]
    \\ `lead (f n) = lead p * lead (f (SUC n))`
    by (
      qpat_x_assum`f n = _`SUBST1_TAC
      \\ irule weak_lead_mult_nonzero
      \\ simp[] )
    \\ rewrite_tac[ring_divides_def]
    \\ metis_tac[])
  \\ `∀n. 0 < n ==>
            lead (f n) IN
            (principal_ideal r (lead (f (SUC n)))).carrier`
  by (
    rpt strip_tac
    \\ DEP_REWRITE_TAC[principal_ideal_element_divides]
    \\ simp[]
    \\ metis_tac[poly_lead_element, poly_ring_element] )
  \\ `∀n. 0 < n ==> (principal_ideal r (lead (f n))).carrier SUBSET
                    (principal_ideal r (lead (f (SUC n)))).carrier`
  by (
    pop_assum mp_tac
    \\ simp[principal_ideal_property]
    \\ simp[SUBSET_DEF, subgroupTheory.coset_def, PULL_EXISTS]
    \\ rw[]
    \\ first_x_assum drule \\ strip_tac
    \\ qexists_tac`z * z'`
    \\ simp[]
    \\ DEP_REWRITE_TAC[ring_mult_assoc]
    \\ conj_tac >- (
      simp[]
      \\ irule poly_lead_element
      \\ fs[poly_ring_element] )
    \\ AP_TERM_TAC
    \\ simp[ring_mult_comm] )
  \\ `∃nm. ∀n. nm <= n ==>
        (principal_ideal r (lead (f n))).carrier =
        (principal_ideal r (lead (f nm))).carrier`
  by (
    spose_not_then strip_assume_tac
    \\ fs[SKOLEM_THM]
    \\ fs[principal_ideal_property]
    \\ `∀n m. 0 < n /\ n <= m ==> lead (f n) * R SUBSET lead (f m) * R`
    by (
      rpt strip_tac
      \\ completeInduct_on`m - n`
      \\ rw[]
      \\ Cases_on`m = n` \\ simp[]
      \\ irule SUBSET_TRANS
      \\ qexists_tac`lead (f (SUC n)) * R`
      \\ conj_tac >- simp[]
      \\ first_x_assum irule
      \\ simp[] )
    \\ `!nm. nm < f' nm` by metis_tac[arithmeticTheory.LESS_OR_EQ]
    \\ first_x_assum(qspec_then`λn. lead (f (FUNPOW f' (SUC n) 0))`mp_tac)
    \\ simp[]
    \\ conj_tac >- metis_tac[poly_lead_element, poly_ring_element]
    \\ simp[arithmeticTheory.FUNPOW_SUC]
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`f m`
    \\ `m <= f' m` by metis_tac[]
    \\ simp[PSUBSET_DEF]
    \\ first_x_assum irule
    \\ simp[]
    \\ simp[Abbr`m`]
    \\ pop_assum kall_tac
    \\ Induct_on`n` \\ rw[]
    \\ rw[arithmeticTheory.FUNPOW_SUC]
    \\ irule arithmeticTheory.LESS_TRANS
    \\ metis_tac[] )
  \\ `∀n. nm <= n ==> ring_associates r (lead (f n)) (lead (f nm))`
  by (
    rpt strip_tac
    \\ DEP_REWRITE_TAC[integral_domain_associates_coset]
    \\ conj_tac >- metis_tac[poly_lead_element, poly_ring_element]
    \\ fs[principal_ideal_property] )
  \\ qmatch_asmsub_abbrev_tac`coset pr.prod _ pr.carrier`
  \\ `coset pr.prod (f (nn + nm)) pr.carrier =
      coset pr.prod (f (SUC (nn +nm))) pr.carrier`
  suffices_by metis_tac[PSUBSET_DEF]
  \\ DEP_REWRITE_TAC[GSYM integral_domain_associates_coset]
  \\ conj_tac >- metis_tac[polyFieldTheory.poly_integral_domain]
  \\ qmatch_goalsub_abbrev_tac`f m`
  \\ `nn <= m /\ nm <= m` by simp[Abbr`m`]
  \\ `f (SUC m) pdivides f m` by metis_tac[]
  \\ pop_assum mp_tac
  \\ rewrite_tac[poly_divides_def]
  \\ strip_tac
  \\ `nn <= SUC m` by simp[]
  \\ `deg (f m) = deg (f (SUC m))` by metis_tac[]
  \\ `poly (f (SUC m))` by metis_tac[poly_ring_element]
  \\ `lead s IN R /\ lead (f (SUC m)) IN R`
  by metis_tac[poly_lead_element]
  \\ `f (SUC m) <> |0|` by metis_tac[]
  \\ `lead (f (SUC m)) <> #0`
  by metis_tac[poly_lead_eq_zero, poly_ring_element]
  \\ `f m <> |0|` by metis_tac[]
  \\ `s <> |0|` by metis_tac[ring_mult_lzero, poly_ring_ring]
  \\ `lead s <> #0` by metis_tac[poly_lead_eq_zero]
  \\ `deg (f m) = deg s + deg (f (SUC m))`
  by (
    qpat_assum`f m = _`SUBST1_TAC
    \\ irule weak_deg_mult_nonzero
    \\ conj_tac >- simp[]
    \\ reverse conj_tac >- simp[]
    \\ metis_tac[IntegralDomain_def] )
  \\ `deg s = 0` by fs[]
  \\ drule_then drule poly_deg_eq_zero
  \\ strip_tac
  \\ BasicProvers.VAR_EQ_TAC
  \\ `f m = h * f (SUC m)` by metis_tac[poly_mult_lconst]
  \\ `lead (f m) = h * lead (f (SUC m))`
  by (
    pop_assum SUBST1_TAC
    \\ irule weak_lead_cmult_nonzero
    \\ conj_tac >- simp[]
    \\ reverse conj_tac >- simp[]
    \\ metis_tac[IntegralDomain_def] )
  \\ `rassoc (lead (f m)) (lead (f nm))` by metis_tac[]
  \\ `nm <= SUC m` by simp[]
  \\ `rassoc (lead (f (SUC m))) (lead (f nm))` by metis_tac[]
  \\ `lead (f nm) IN r.carrier`
  by metis_tac[poly_lead_element, poly_ring_element]
  \\ `rassoc (lead (f nm)) (lead (f (SUC m)))`
  by metis_tac[ring_associates_sym]
  \\ `rassoc (lead (f m)) (lead (f (SUC m)))`
  by ( irule ring_associates_trans \\ metis_tac[] )
  \\ `∃u. unit u /\ lead (f m) = u * lead (f (SUC m))`
  by metis_tac[ring_associates_def]
  \\ `u IN R` by metis_tac[ring_unit_property]
  \\ `u = h` by metis_tac[integral_domain_mult_rcancel]
  \\ rewrite_tac[ring_associates_def]
  \\ qexists_tac`[h]`
  \\ qunabbrev_tac`pr`
  \\ reverse conj_tac >- metis_tac[]
  \\ `upoly |1|` by simp[poly_unit_one]
  \\ `|1| = [#1]` by simp[poly_one]
  \\ `[h] = u * [#1]` by (
    DEP_REWRITE_TAC[poly_cmult_const_nonzero]
    \\ simp[] )
  \\ pop_assum SUBST1_TAC
  \\ irule poly_unit_cmult
  \\ metis_tac[]
QED

Theorem ufd_factors:
  UniqueFactorizationDomain r /\
  a IN ring_nonzero r /\ ~Unit r a /\ Unit r u /\
  FINITE_BAG ps /\ BAG_EVERY (irreducible r) ps /\
  a = r.prod.op u (GBAG r.prod ps) /\
  b IN r.carrier /\ ring_divides r b a
  ==>
  ?qs. qs <= ps /\ ring_associates r b (GBAG r.prod qs)
Proof
  rpt strip_tac
  \\ drule ufd_atomic \\ strip_tac
  \\ drule atomic_unique_ufd
  \\ disch_then(drule o #2 o EQ_IMP_RULE)
  \\ fs[ring_divides_def]
  \\ `IntegralDomain r` by metis_tac[UniqueFactorizationDomain_def]
  \\ `Ring r` by metis_tac[IntegralDomain_def]
  \\ strip_tac
  \\ Cases_on`s = r.sum.id` \\ gs[]
  >- fs[ring_nonzero_eq]
  \\ Cases_on`Unit r s`
  >- (
    qexists_tac`ps`
    \\ simp[]
    \\ simp[ring_associates_def]
    \\ qexists_tac`r.prod.op ( |/ s) u`
    \\ `Unit r ( |/ s)` by simp[ring_unit_has_inv]
    \\ simp[ring_unit_mult_unit]
    \\ DEP_REWRITE_TAC[ring_mult_assoc]
    \\ simp[]
    \\ conj_asm1_tac
    >- (
      irule ring_product_element
      \\ simp[]
      \\ fs[BAG_EVERY, SUBSET_DEF, irreducible_element] )
    \\ qpat_x_assum`s * b = _`(SUBST1_TAC o SYM)
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ simp[ring_unit_linv])
  \\ `∃su sps. unit su ∧ FINITE_BAG sps ∧
               BAG_EVERY (λp. rprime p /\ p <> #0 /\ p NOTIN R* ) sps /\
               SET_OF_BAG sps SUBSET R /\ s = su * GBAG r.prod sps`
  by metis_tac[UniqueFactorizationDomain_def]
  \\ Cases_on`b = #0`
  >- gs[ring_nonzero_eq]
  \\ Cases_on`unit b`
  >- (
    qexists_tac`{||}`
    \\ simp[]
    \\ simp[ring_associates_def]
    \\ qexists_tac`b`
    \\ simp[] )
  \\ `∃bu bps. unit bu ∧ FINITE_BAG bps ∧
               BAG_EVERY (λp. rprime p /\ p <> #0 /\ p NOTIN R* ) bps /\
               SET_OF_BAG bps SUBSET R /\ b = bu * GBAG r.prod bps`
  by metis_tac[UniqueFactorizationDomain_def]
  \\ first_x_assum(qspecl_then[`BAG_TO_LIST ps`,
       `BAG_TO_LIST sps ++ BAG_TO_LIST bps`]mp_tac)
  \\ impl_keep_tac
  >- (
    simp[EVERY_MEM, MEM_BAG_TO_LIST]
    \\ fs[BAG_EVERY]
    \\ fs[SUBSET_DEF]
    \\ conj_tac >- metis_tac[prime_is_irreducible]
    \\ simp[BAG_TO_LIST_INV, LIST_TO_BAG_APPEND]
    \\ DEP_REWRITE_TAC[GBAG_UNION]
    \\ simp[SUBSET_DEF]
    \\ conj_tac >- metis_tac[Ring_def]
    \\ simp[ring_associates_def]
    \\ qexists_tac`|/ u * su * bu`
    \\ DEP_REWRITE_TAC[ring_unit_mult_unit]
    \\ simp[ring_unit_has_inv]
    \\ qmatch_asmsub_abbrev_tac`rhs = u * pps`
    \\ `|/ u * (u * pps) = |/ u * rhs` by simp[]
    \\ pop_assum mp_tac
    \\ DEP_REWRITE_TAC[GSYM ring_mult_assoc]
    \\ simp[ring_unit_linv]
    \\ conj_asm1_tac
    >- (
      simp[Abbr`pps`, ring_unit_inv_element]
      \\ rpt conj_tac
      \\ `r.carrier = r.prod.carrier` by simp[]
      \\ pop_assum SUBST1_TAC
      \\ irule GBAG_in_carrier
      \\ simp[SUBSET_DEF]
      \\ fs[irreducible_def, ring_nonzero_eq]
      \\ metis_tac[Ring_def] )
    \\ qpat_x_assum`_  * _ = u * pps`(assume_tac o SYM)
    \\ simp[]
    \\ strip_tac
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ simp[]
    \\ AP_TERM_TAC
    \\ simp[Abbr`rhs`]
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ simp[]
    \\ AP_TERM_TAC
    \\ simp[Once ring_mult_comm]
    \\ DEP_REWRITE_TAC[ring_mult_assoc] \\ simp[]
    \\ AP_TERM_TAC
    \\ simp[Once ring_mult_comm])
  \\ strip_tac
  \\ drule LIST_REL_PERM
  \\ disch_then(qspec_then`BAG_TO_LIST sps ++ BAG_TO_LIST bps`mp_tac)
  \\ impl_tac >- metis_tac[PERM_SYM]
  \\ rw[LIST_REL_SPLIT2]
  \\ qexists_tac`LIST_TO_BAG ys2`
  \\ `LIST_TO_BAG (BAG_TO_LIST ps) = LIST_TO_BAG (ys1 ++ ys2)`
  by metis_tac[PERM_LIST_TO_BAG]
  \\ `ps = BAG_UNION (LIST_TO_BAG ys1) (LIST_TO_BAG ys2)`
  by metis_tac[LIST_TO_BAG_APPEND, BAG_TO_LIST_INV]
  \\ pop_assum SUBST1_TAC
  \\ simp[]
  \\ `GBAG r.prod (LIST_TO_BAG ys2) IN r.prod.carrier`
  by (
    irule GBAG_in_carrier
    \\ simp[SUBSET_DEF, IN_LIST_TO_BAG]
    \\ imp_res_tac MEM_PERM
    \\ gs[MEM_BAG_TO_LIST]
    \\ fs[BAG_EVERY, irreducible_def, ring_nonzero_eq]
    \\ metis_tac[Ring_def] )
  \\ irule ring_associates_trans
  \\ rfs[]
  \\ qexists_tac`GBAG r.prod bps`
  \\ conj_tac
  >- ( simp[ring_associates_def] \\ metis_tac[] )
  \\ `bps = LIST_TO_BAG (BAG_TO_LIST bps)` by metis_tac[BAG_TO_LIST_INV]
  \\ pop_assum SUBST1_TAC
  \\ irule LIST_REL_ring_associates_product
  \\ simp[]
  \\ conj_asm1_tac
  >- (
    imp_res_tac MEM_PERM
    \\ gs[MEM_BAG_TO_LIST, SUBSET_DEF]
    \\ fs[BAG_EVERY, irreducible_def, ring_nonzero_eq] )
  \\ fs[LIST_REL_EL_EQN]
  \\ rw[]
  \\ first_x_assum(qspec_then`n`mp_tac)
  \\ simp[] \\ strip_tac
  \\ irule ring_associates_sym
  \\ simp[]
  \\ fs[SUBSET_DEF]
  \\ metis_tac[MEM_BAG_TO_LIST, MEM_EL]
QED

Theorem UniqueFactorizationDomain_PolyRing =
mk_oracle_thm"ufdpoly"([],``
  !r. UniqueFactorizationDomain r ==>
      UniqueFactorizationDomain (PolyRing r)
``)

Theorem UniqueFactorizationDomain_mpoly:
  !s. FINITE s ==>
      !r. UniqueFactorizationDomain r ==>
          UniqueFactorizationDomain (mpoly_ring r s)
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  >- (
    `Ring r` by fs[integral_domain_is_ring, UniqueFactorizationDomain_def]
    \\ `Ring (mpoly_ring r {})` by simp[]
    \\ `∃f. RingIso f r (mpoly_ring r {})`
    suffices_by metis_tac[UniqueFactorizationDomain_RingIso]
    \\ metis_tac[mpoly_ring_empty_support_iso, ring_iso_sym] )
  \\ `Ring r` by fs[UniqueFactorizationDomain_def, integral_domain_is_ring]
  \\ `e IN (e INSERT s) /\ (e INSERT s) DELETE e = s`
  by ( simp[Once EXTENSION] \\ metis_tac[] )
  \\ `Ring (mpoly_ring r (e INSERT s))` by simp[]
  \\ `Ring (PolyRing (mpoly_ring r s))` by simp[poly_ring_ring]
  \\ `∃f. RingIso f (PolyRing (mpoly_ring r s)) (mpoly_ring r (e INSERT s))`
  by metis_tac[RingIso_mpoly_ring_poly_ring, ring_iso_sym]
  \\ metis_tac[UniqueFactorizationDomain_RingIso,
               UniqueFactorizationDomain_PolyRing]
QED

(* -- *)

Definition mono_bag_def:
  mono_bag c s = BAG_IMAGE (flip part s) (BAG_OF_SET c)
End

Theorem BAG_IN_mono_bag:
  FINITE c ⇒
  (x <: mono_bag c s <=> ∃b. b ∈ c ∧ x = part b s)
Proof
  rw[mono_bag_def] \\ metis_tac[]
QED

Theorem mono_bag_itset:
  !c. FINITE c ==>
  !s. mono_bag c s = ITSET (λb. BAG_INSERT (part b s)) c {||}
Proof
  simp[mono_bag_def, BAG_IMAGE_BAG_OF_SET_ITSET_BAG_INSERT]
  \\ srw_tac[ETA_ss][]
QED

Theorem mono_bag_empty[simp]:
  mono_bag {} x = {||}
Proof
  rw[mono_bag_def]
QED

Theorem mono_bag_inj:
  FINITE b ∧ b factorises w ∧ x ∈ w ∧ y ∈ w ∧
  mono_bag b x = mono_bag b y ⇒ x = y
Proof
  rw[]
  \\ DEP_REWRITE_TAC[factorises_distinguish]
  \\ rw[]
  \\ `part v x <: mono_bag b y` by metis_tac[BAG_IN_mono_bag]
  \\ `∃u. u ∈ b ∧ part v x = part u y` by metis_tac[BAG_IN_mono_bag]
  \\ `u partitions w ∧ v partitions w` by fs[factorises_def]
  \\ irule part_unique
  \\ reverse conj_tac >- metis_tac[part_in_partition]
  \\ metis_tac[in_part]
QED

Definition mono_bag_poly_def:
  mono_bag_poly (b:'v bag bag) t = &(b t) : real
End

Theorem monomials_mono_bag_poly[simp]:
  monomials Reals (mono_bag_poly b) = SET_OF_BAG b
Proof
  rw[monomials_def, mono_bag_poly_def, SET_OF_BAG]
  \\ rw[Once FUN_EQ_THM, BAG_IN, BAG_INN]
  \\ rw[rrestrict_def, Reals_def]
QED

Theorem mpoly_mono_bag_poly[simp]:
  FINITE_BAG b ==>
  mpoly Reals (mono_bag_poly b)
Proof
  rw[mpoly_def, SUBSET_DEF]
  \\ rw[mono_bag_poly_def, Reals_def]
QED

Theorem support_mono_bag_poly[simp]:
  support Reals (mono_bag_poly b) = BIGUNION (IMAGE SET_OF_BAG (SET_OF_BAG b))
Proof
  rw[support_def]
QED

Theorem mono_bag_poly_sing:
  mono_bag_poly {|x|} t = if x = t then 1 else 0
Proof
  rw[mono_bag_poly_def]
  \\ simp[BAG_INSERT, EMPTY_BAG]
QED

Theorem mono_bag_poly_inj[simp]:
  mono_bag_poly b1 = mono_bag_poly b2 <=> b1 = b2
Proof
  rw[mono_bag_poly_def, Once FUN_EQ_THM]
  \\ rw[FUN_EQ_THM]
QED

Theorem mono_bag_poly_insert:
  mono_bag_poly (BAG_INSERT x b) = mpoly_add Reals (mono_bag_poly {|x|}) (mono_bag_poly b)
Proof
  rw[mono_bag_poly_def, Once FUN_EQ_THM]
  \\ rw[mpoly_add_def, Reals_def, rrestrict_def]
  \\ rw[mono_bag_poly_def]
  \\ rw[BAG_INSERT, EMPTY_BAG]
QED

Theorem mono_bag_poly_BAG_OF_SET:
  !s. FINITE s ==> !supp. BIGUNION (IMAGE SET_OF_BAG s) SUBSET supp ==>
  mono_bag_poly (BAG_OF_SET s) =
  GBAG (mpoly_ring Reals supp).sum (BAG_IMAGE (mono_bag_poly o EL_BAG) (BAG_OF_SET s))
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  >- rw[mpoly_ring_def, mono_bag_poly_def, FUN_EQ_THM, EMPTY_BAG, Reals_def]
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ simp[Once mono_bag_poly_insert]
  \\ DEP_REWRITE_TAC[GITBAG_INSERT_THM]
  \\ simp[]
  \\ conj_asm1_tac >- (
    fs[SUBSET_DEF, PULL_EXISTS]
    \\ simp[mpoly_ring_def, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ DEP_ONCE_REWRITE_TAC[GITBAG_GBAG]
  \\ simp[]
  \\ simp[Once mpoly_ring_def, EL_BAG]
  \\ metis_tac[]
QED

Definition mono_def:
  mono c s = mono_bag_poly {|mono_bag c s|}
End

Theorem monomials_mono[simp]:
  monomials Reals (mono c s) = {mono_bag c s}
Proof
  rw[monomials_def, mono_def, mono_bag_poly_sing]
  \\ rw[Once EXTENSION]
  \\ rw[rrestrict_def, Reals_def]
QED

Theorem support_mono[simp]:
  support Reals (mono c s) = IMAGE (flip part s) c
Proof
  rw[support_def, monomials_mono, mono_bag_def]
QED

Theorem support_mpoly_mul_mono:
  FINITE c1 ∧ FINITE c2 ⇒
  support Reals (mpoly_mul Reals (mono c1 s1) (mono c2 s2)) =
  support Reals (mono c1 s1) ∪ support Reals (mono c2 s2)
Proof
  qho_match_abbrev_tac`P c1 c2 ==> a c1 s1 c2 s2 = b c1 s1 UNION b c2 s2`
  \\ `!c1 c2 s1 s2. P c1 c2 ==> b c1 s1 SUBSET a c1 s1 c2 s2` suffices_by (
    unabbrev_all_tac \\ simp[]
    \\ rpt strip_tac
    \\ simp[SET_EQ_SUBSET]
    \\ conj_tac >- metis_tac[support_mpoly_mul_SUBSET, RingReals, support_mono]
    \\ DEP_ONCE_REWRITE_TAC[mpoly_mul_comm]
    \\ simp[] )
  \\ rw[Abbr`P`,Abbr`a`,Abbr`b`]
  \\ simp[SUBSET_DEF, PULL_EXISTS]
  \\ simp[support_def, monomials_def, PULL_EXISTS]
  \\ simp[rrestrict_mpoly_mul]
  \\ simp[mpoly_mul_BAG_FILTER_cross]
  \\ simp[mono_def, mono_bag_poly_sing]
  \\ simp[BAG_FILTER_BAG_OF_SET]
  \\ qx_gen_tac`t1` \\ strip_tac
  \\ qexists_tac`BAG_UNION (mono_bag c1 s1) (mono_bag c2 s2)`
  \\ simp[Once mono_bag_def]
  \\ conj_tac >- metis_tac[]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ `s = {(mono_bag c1 s1, mono_bag c2 s2)}`
  by (
    simp[Abbr`s`, Once EXTENSION, FORALL_PROD]
    \\ metis_tac[] )
  \\ rw[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ rw[rrestrict_def, Reals_def]
QED

Theorem support_mono_inj:
  FINITE b ∧ b factorises w ∧ c ⊆ b ∧ s1 ∈ w ∧ s2 ∈ w ∧
  support Reals (mono c s1) = support Reals (mono c s2) ==> mono c s1 = mono c s2
Proof
  rw[mono_def, mono_bag_def]
  \\ irule BAG_IMAGE_CONG \\ simp[]
  \\ `FINITE c` by metis_tac[SUBSET_FINITE]
  \\ fs[Once EXTENSION]
  \\ gen_tac \\ strip_tac
  \\ simp[GSYM EXTENSION]
  \\ irule part_unique
  \\ reverse conj_tac
  >- metis_tac[part_in_partition, SUBSET_DEF, factorises_def]
  \\ metis_tac[in_part, factorises_def, SUBSET_DEF]
QED

Definition monos_def:
  monos c e = IMAGE (mono c) e
End

Theorem FINITE_monos[simp]:
  FINITE e ==> FINITE (monos c e)
Proof
  rw[monos_def]
QED

Definition char_poly_def:
  char_poly b e = mono_bag_poly (BAG_IMAGE (mono_bag b) (BAG_OF_SET e))
End

Definition ffs_poly_def:
  ffs_poly c e = mono_bag_poly (BAG_OF_SET (IMAGE (mono_bag c) e))
End

Theorem monomials_ffs_poly[simp]:
  monomials Reals (ffs_poly c e) = IMAGE (mono_bag c) e
Proof
  rw[ffs_poly_def, mono_bag_def]
QED

Theorem char_poly_ffs_poly:
  FINITE b ∧ b factorises w ∧ FINITE e ∧ e ⊆ w ⇒
  char_poly b e = ffs_poly b e
Proof
  strip_tac
  \\ simp[ffs_poly_def, char_poly_def]
  \\ DEP_REWRITE_TAC[BAG_OF_SET_IMAGE_INJ]
  \\ metis_tac[mono_bag_inj, SUBSET_DEF]
QED

Theorem monomials_char_poly[simp]:
  monomials Reals (char_poly b e) = IMAGE (mono_bag b) e
Proof
  rw[char_poly_def]
QED

Theorem support_char_poly[simp]:
  support Reals (char_poly b e) = IMAGE (UNCURRY part) (b × e)
Proof
  rw[support_def]
  \\ rw[GSYM IMAGE_COMPOSE, combinTheory.o_DEF]
  \\ rw[mono_bag_def]
  \\ rw[Once EXTENSION, PULL_EXISTS, EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem char_poly_eq_zero:
  FINITE e ==>
  (char_poly b e = K 0 <=> e = {})
Proof
  rw[char_poly_def, Once FUN_EQ_THM, mono_bag_poly_def, BAG_IMAGE_DEF]
  \\ simp[BCARD_0]
  \\ simp[BAG_FILTER_EQ_EMPTY, BAG_EVERY]
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Theorem mpoly_char_poly[simp]:
  FINITE e ==>
  mpoly Reals (char_poly b e)
Proof
  rw[char_poly_def]
QED

Theorem mpoly_ffs_poly[simp]:
  FINITE e ==> mpoly Reals (ffs_poly b e)
Proof
  rw[ffs_poly_def]
QED

Theorem mono_chim:
  FINITE b ∧ b factorises w ∧ s ∈ w ∧ t ∈ w ∧ c ⊆ b ⇒
  mono c (chim w b c s t) = mono c s
Proof
  rw[mono_def]
  \\ rw[mono_bag_def]
  \\ irule BAG_IMAGE_CONG
  \\ rw[]
  \\ `x IN b` by fs[SUBSET_DEF]
  \\ rw[chim_thm]
QED

Theorem mono_chim_other:
  b factorises w ∧ s ∈ w ∧ t ∈ w ∧ DISJOINT c d ∧ d ⊆ b ⇒
  mono d (chim w b c s t) = mono d t
Proof
  rw[mono_def, mono_bag_def]
  \\ irule BAG_IMAGE_CONG
  \\ rw[]
  \\ `x IN b` by fs[SUBSET_DEF]
  \\ rw[chim_thm]
  \\ fs[IN_DISJOINT]
  \\ metis_tac[]
QED

Theorem mpoly_mul_mono_chim_disjoint_union:
  FINITE c ∧ FINITE d ∧ DISJOINT c d ⇒
  mpoly_mul Reals (mono c (chim w b c s t)) (mono d (chim w b c s t)) =
  mono (c ∪ d) (chim w b c s t)
Proof
  rw[mono_def]
  \\ simp[Once FUN_EQ_THM] \\ gen_tac
  \\ DEP_REWRITE_TAC[mpoly_mul_BAG_FILTER_cross]
  \\ simp[]
  \\ simp[mono_bag_poly_sing]
  \\ simp[mono_bag_def]
  \\ gs[BAG_OF_SET_DISJOINT_UNION, BAG_FILTER_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`{u}`
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE _ (BAG_OF_SET uu)`
  \\ qmatch_goalsub_abbrev_tac`COND xx`
  \\ `uu = if xx then {u} else {}`
  by (
    unabbrev_all_tac \\ simp[Once EXTENSION, FORALL_PROD]
    \\ rw[] \\ metis_tac[] )
  \\ rw[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ rw[Reals_def, rrestrict_def, Abbr`u`]
QED

Theorem prod_monos_union_chim:
  FINITE b ∧ b factorises w ∧ e1 ⊆ w ∧ e2 ⊆ w ∧ c1 ⊆ b ∧ c2 ⊆ b ∧ DISJOINT c1 c2 ⇒
  IMAGE (UNCURRY (mpoly_mul Reals)) (monos c1 e1 × monos c2 e2) ⊆
  monos (c1 ∪ c2) (IMAGE (UNCURRY (chim w b c1)) (e1 × e2))
Proof
  strip_tac
  \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ simp[monos_def, PULL_EXISTS, EXISTS_PROD]
  \\ qx_genl_tac[`s1`,`s2`] \\ strip_tac
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ `FINITE c1 ∧ FINITE c2` by metis_tac[SUBSET_FINITE]
  \\ simp[GSYM mpoly_mul_mono_chim_disjoint_union]
  \\ `s1 ∈ w ∧ s2 ∈ w` by metis_tac[SUBSET_DEF]
  \\ simp[mono_chim, mono_chim_other]
QED

Theorem BIJ_poly_mul_chim:
  FINITE b ∧ b factorises w ∧ e1 ⊆ w ∧ e2 ⊆ w ∧ c1 ⊆ b ∧ c2 ⊆ b ∧ DISJOINT c1 c2
  ⇒
  BIJ (UNCURRY (mpoly_mul Reals))
    (monos c1 e1 × monos c2 e2)
    (monos (c1 ∪ c2) (IMAGE (λ(s,t). chim w b c1 s t) (e1 × e2)))
Proof
  strip_tac
  \\ simp[BIJ_DEF]
  \\ qmatch_goalsub_abbrev_tac`INJ f s t`
  \\ `!x. x IN s ==> f x IN t`
  by (
    drule prod_monos_union_chim
    \\ unabbrev_all_tac
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ fs[SUBSET_DEF])
  \\ reverse conj_tac
  >- (
    simp[SURJ_DEF, Abbr`t`, monos_def, PULL_EXISTS, FORALL_PROD]
    \\ simp[Abbr`s`, EXISTS_PROD]
    \\ simp[monos_def, PULL_EXISTS]
    \\ simp[Abbr`f`]
    \\ qx_genl_tac[`s`,`t`] \\ strip_tac
    \\ qexistsl_tac[`s`,`t`] \\ simp[]
    \\ DEP_REWRITE_TAC[GSYM mpoly_mul_mono_chim_disjoint_union]
    \\ conj_tac >- metis_tac[SUBSET_FINITE]
    \\ `s ∈ w ∧ t ∈ w` by metis_tac[SUBSET_DEF]
    \\ metis_tac[mono_chim, mono_chim_other])
  \\ simp[INJ_DEF]
  \\ simp[Abbr`s`, FORALL_PROD, Abbr`f`]
  \\ qx_genl_tac[`m1`,`m2`,`n1`,`n2`]
  \\ strip_tac
  \\ strip_tac
  \\ `∀m1 m2. m1 ∈ monos c1 e1 ∧ m2 ∈ monos c2 e2 ⇒
              support Reals m1 = support Reals (mpoly_mul Reals m1 m2) INTER BIGUNION c1 ∧
              support Reals m2 = support Reals (mpoly_mul Reals m1 m2) INTER BIGUNION c2`
  by (
    simp[monos_def, PULL_EXISTS, support_mono]
    \\ `FINITE c1 ∧ FINITE c2` by metis_tac[SUBSET_FINITE]
    \\ qx_genl_tac[`s1`,`s2`]
    \\ strip_tac
    \\ simp[support_mpoly_mul_mono]
    \\ `IMAGE (flip part s1) c1 ⊆ BIGUNION c1 ∧
        IMAGE (flip part s2) c2 ⊆ BIGUNION c2`
    by (
      simp[SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[part_in_partition, SUBSET_DEF, factorises_def] )
    \\ `DISJOINT (BIGUNION c1) (BIGUNION c2)`
    by (
      rw[IN_DISJOINT]
      \\ CCONTR_TAC \\ fs[]
      \\ qmatch_asmsub_rename_tac`t1 ∈ c1`
      \\ qmatch_asmsub_rename_tac`t2 ∈ c2`
      \\ `t1 <> t2` by metis_tac[IN_DISJOINT]
      \\ `DISJOINT t1 t2` by metis_tac[factors_DISJOINT, SUBSET_DEF]
      \\ metis_tac[IN_DISJOINT])
    \\ qmatch_goalsub_abbrev_tac`a1 = (a1 ∪ a2) INTER b1`
    \\ qmatch_asmsub_abbrev_tac`DISJOINT b1 b2`
    \\ qpat_x_assum`DISJOINT _ _`mp_tac
    \\ ntac 2 (qpat_x_assum`_ ⊆ _`mp_tac)
    \\ simp[IN_DISJOINT, SUBSET_DEF, SET_EQ_SUBSET]
    \\ metis_tac[])
  \\ `support Reals m1 = support Reals n1` by metis_tac[]
  \\ `support Reals m2 = support Reals n2` by metis_tac[]
  \\ fs[monos_def]
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ conj_tac \\ irule support_mono_inj
  \\ metis_tac[SUBSET_DEF]
QED

Theorem support_ffs_poly:
  support Reals (ffs_poly c e) =
  BIGUNION (IMAGE (flip IMAGE c o flip part) e)
Proof
  rw[support_def]
  \\ rw[GSYM IMAGE_COMPOSE]
  \\ rw[combinTheory.o_DEF]
  \\ simp[mono_bag_def]
QED

Theorem mpoly_mul_ffs_poly:
  FINITE w ∧ b factorises w ∧ e1 ⊆ w ∧ e2 ⊆ w ∧ c1 ⊆ b ∧ c2 ⊆ b ∧ DISJOINT c1 c2 ∧
  IMAGE (UNCURRY (mpoly_mul Reals )) (monos c1 e1 × monos c2 e2)
  SUBSET (mpoly_ring Reals supp).carrier
  ⇒
  mpoly_mul Reals (ffs_poly c1 e1) (ffs_poly c2 e2) =
  GBAG (mpoly_ring Reals supp).sum
    (BAG_IMAGE (UNCURRY (mpoly_mul Reals))
               (BAG_OF_SET (monos c1 e1 × monos c2 e2)))
Proof
  strip_tac
  \\ simp[Once FUN_EQ_THM] \\ gen_tac
  \\ DEP_REWRITE_TAC[mpoly_mul_BAG_FILTER_cross]
  \\ simp[]
  \\ `FINITE e1 ∧ FINITE e2` by metis_tac[SUBSET_FINITE] \\ simp[]
  \\ DEP_REWRITE_TAC[MP_CANON mpoly_ring_sum_applied]
  \\ simp[]
  \\ simp[monos_def]
  \\ simp[GSYM BAG_IMAGE_COMPOSE]
  \\ simp[combinTheory.o_DEF, LAMBDA_PROD]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET l1`
  \\ qmatch_goalsub_abbrev_tac`_ = _ _ (_ _ (_ l2)) _`
  \\ `l2 = IMAGE (λ(x,y). (mono_bag_poly {|x|}, mono_bag_poly{|y|})) l1`
  by (
    simp[Abbr`l1`, Abbr`l2`]
    \\ simp[Once EXTENSION, EXISTS_PROD, PULL_EXISTS, FORALL_PROD]
    \\ simp[mono_def]
    \\ metis_tac[] )
  \\ fs[Abbr`l2`]
  \\ qmatch_goalsub_abbrev_tac`BAG_IMAGE p (BAG_OF_SET (IMAGE f l1))`
  \\ irule EQ_TRANS
  \\ qexists_tac`GBAG Reals.sum (BAG_IMAGE p (BAG_IMAGE f (BAG_OF_SET l1)))`
  \\ reverse conj_tac
  >- (
    AP_THM_TAC \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ irule EQ_SYM
    \\ irule BAG_OF_SET_IMAGE_INJ
    \\ simp[Abbr`f`, Abbr`l1`, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] )
  \\ DEP_REWRITE_TAC[MP_CANON GBAG_IMAGE_FILTER]
  \\ simp[]
  \\ conj_asm1_tac
  >- ( simp[Abbr`l1`, SUBSET_DEF, PULL_EXISTS, FORALL_PROD] )
  \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
  \\ conj_tac >- simp[Abbr`l1`]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule BAG_IMAGE_CONG
  \\ simp[Abbr`p`, Abbr`f`, FORALL_PROD]
  \\ simp[mpoly_mul_BAG_FILTER_cross]
  \\ simp[mono_bag_poly_sing]
  \\ simp[BAG_FILTER_BAG_OF_SET, LAMBDA_PROD]
  \\ simp[Abbr`l1`, PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
  \\ qmatch_goalsub_abbrev_tac`x = BAG_UNION b1 b2`
  \\ `s = if x = BAG_UNION b1 b2 then {(b1,b2)} else {}`
  by (
    simp[Abbr`s`, Once EXTENSION, FORALL_PROD]
    \\ rw[] \\ metis_tac[] )
  \\ IF_CASES_TAC \\ gs[]
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ simp[ffs_poly_def, Abbr`b1`, Abbr`b2`, mono_bag_poly_def]
  \\ simp[rrestrict_def, Reals_def]
  \\ simp[BAG_OF_SET] \\ rw[]
  \\ metis_tac[]
QED

Theorem ffs_poly_union_chim_mul:
  FINITE w ∧ b factorises w ∧ e1 ⊆ w ∧ e2 ⊆ w ∧ c1 ⊆ b ∧ c2 ⊆ b ∧ DISJOINT c1 c2 ⇒
    ffs_poly (c1 ∪ c2) (IMAGE (UNCURRY (chim w b c1)) (e1 × e2)) =
    mpoly_mul Reals (ffs_poly c1 e1) (ffs_poly c2 e2)
Proof
  strip_tac
  \\ `FINITE e1 ∧ FINITE e2` by metis_tac[SUBSET_FINITE]
  \\ DEP_REWRITE_TAC[Q.SPEC`UNIV`(Q.GEN`supp`mpoly_mul_ffs_poly)]
  \\ simp[]
  \\ simp[Once mpoly_ring_def]
  \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
  \\ conj_tac >- (
    simp[monos_def, PULL_EXISTS] \\ rw[]
    \\ irule mpoly_mpoly_mul
    \\ simp[] )
  \\ simp[ffs_poly_def]
  \\ DEP_REWRITE_TAC[Q.SPEC`UNIV`(Q.GEN`supp`(SPEC_ALL(MP_CANON mono_bag_poly_BAG_OF_SET)))]
  \\ simp[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ DEP_ONCE_REWRITE_TAC[GSYM BAG_OF_SET_IMAGE_INJ]
  \\ simp[PULL_EXISTS, FORALL_PROD, EL_BAG]
  \\ simp[Once (GSYM IMAGE_COMPOSE)]
  \\ simp[combinTheory.o_DEF, EL_BAG]
  \\ simp[GSYM mono_def]
  \\ srw_tac[ETA_ss][GSYM monos_def]
  \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s2 = BAG_IMAGE f (BAG_OF_SET s1)`
  \\ `BIJ f s1 s2` by metis_tac[BIJ_poly_mul_chim, factorises_FINITE]
  \\ `s2 = IMAGE f s1` by metis_tac[BIJ_IMAGE]
  \\ pop_assum SUBST1_TAC
  \\ irule BAG_OF_SET_IMAGE_INJ
  \\ metis_tac[BIJ_DEF, INJ_DEF]
QED

Theorem degree_of_char_poly:
  FINITE b ∧ b factorises w ∧ FINITE e ∧ e ⊆ w ⇒
  degree_of Reals (char_poly b e) v <= 1
Proof
  rw[char_poly_def, degree_of_def]
  \\ simp[GSYM IMAGE_COMPOSE, combinTheory.o_DEF]
  \\ qmatch_goalsub_abbrev_tac`MAX_SET s`
  \\ `s ⊆ {0; 1}`
  by (
    simp[Abbr`s`, SUBSET_DEF, PULL_EXISTS]
    \\ simp[mono_bag_def]
    \\ rw[BAG_IMAGE_DEF]
    \\ rw[BAG_FILTER_BAG_OF_SET]
    \\ simp[BAG_CARD_BAG_OF_SET]
    \\ qmatch_goalsub_abbrev_tac`a ∨ _`
    \\ Cases_on`a = T` \\ fs[Abbr`a`]
    \\ fs[GSYM MEMBER_NOT_EMPTY] \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`CARD s`
    \\ `s = {x}` suffices_by rw[]
    \\ simp[Abbr`s`, Once SET_EQ_SUBSET]
    \\ simp[SUBSET_DEF]
    \\ rw[]
    \\ CCONTR_TAC
    \\ drule factors_DISJOINT
    \\ qmatch_asmsub_rename_tac`part b1 s = part b2 s`
    \\ simp[]
    \\ qexistsl_tac[`b1`,`b2`] \\ simp[]
    \\ simp[IN_DISJOINT]
    \\ metis_tac[part_in_partition, SUBSET_DEF, factorises_def] )
  \\ `1 = MAX_SET {0; 1}` by EVAL_TAC
  \\ pop_assum SUBST1_TAC
  \\ irule SUBSET_MAX_SET
  \\ reverse conj_asm2_tac >- simp[]
  \\ metis_tac[SUBSET_FINITE]
QED

Theorem char_poly_unique_parts:
  FINITE b ∧ FINITE e ∧ b factorises w ∧ e ⊆ w ∧
  x ∈ b ∧ t IN monomials Reals (char_poly b e) ⇒
    ∃!s. s ∈ x ∧ BAG_IN s t
Proof
  rw[mono_bag_def]
  \\ rw[EXISTS_UNIQUE_THM, PULL_EXISTS]
  \\ qexists_tac`x` \\ simp[]
  \\ qmatch_assum_rename_tac`y IN e`
  \\ `y ∈ w` by fs[SUBSET_DEF]
  \\ `x partitions w` by fs[factorises_def]
  \\ conj_tac >- metis_tac[part_in_partition]
  \\ qx_genl_tac[`v1`,`v2`]
  \\ strip_tac
  \\ irule part_unique
  \\ `v1 partitions w ∧ v2 partitions w` by fs[factorises_def]
  \\ metis_tac[in_part, part_unique, part_in_partition]
QED

Theorem char_poly_empty:
  FINITE e ==>
  char_poly {} e = λt. if t = {||} then &CARD e else 0
Proof
  rw[char_poly_def, FUN_EQ_THM, mono_bag_poly_def]
  \\ rw[BAG_IMAGE_DEF, BAG_FILTER_BAG_OF_SET, BAG_CARD_BAG_OF_SET]
  \\ rw[EXTENSION]
  \\ AP_TERM_TAC
  \\ rw[EXTENSION, FUN_EQ_THM]
QED

Theorem mono_bag_SUB_BAG:
  c SUBSET b /\ FINITE b ==>
  mono_bag c x <= mono_bag b x
Proof
  strip_tac
  \\ `FINITE c` by metis_tac[SUBSET_FINITE]
  \\ rw[SUB_BAG, BAG_INN, mono_bag_def, BAG_IMAGE_DEF,
        BAG_FILTER_BAG_OF_SET, BAG_CARD_BAG_OF_SET]
  \\ fs[arithmeticTheory.GREATER_EQ]
  \\ irule arithmeticTheory.LESS_EQ_TRANS
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ irule CARD_SUBSET
  \\ fs[SUBSET_DEF]
QED

Theorem divides_char_poly_multiple_ffs_poly:
  FINITE w ∧ b factorises w ∧ e ⊆ w ∧ e ≠ ∅ ∧
  mpoly Reals p ∧ mpoly Reals q ∧
  FINITE (support Reals p) /\ FINITE (support Reals q) /\
  mpoly_mul Reals p q = char_poly b e ⇒
  ∃r c. p = (($* r) o ffs_poly c e) ∧ c ⊆ b
Proof
  strip_tac
  \\ `FINITE e` by metis_tac[SUBSET_FINITE]
  \\ `FINITE b` by metis_tac[factorises_FINITE]
  \\ `p <> K Reals.sum.id /\ q <> K Reals.sum.id`
  by (
    CCONTR_TAC
    \\ `char_poly b e = K Reals.sum.id`
    by metis_tac[monomials_zero, imp_mpoly_mul_zero]
    \\ pop_assum mp_tac
    \\ simp[Reals_def, char_poly_eq_zero] )
  \\ `IntegralDomain Reals` by
  metis_tac[fieldTheory.field_is_integral_domain, FieldReals]
  \\ `support Reals p ∪ support Reals q = support Reals (char_poly b e)`
  by (
    irule EQ_SYM
    \\ qpat_assum`_ = char_poly _ _`(SUBST1_TAC o SYM)
    \\ irule support_mpoly_mul \\ simp[] )
  \\ `∀v. degree_of Reals (char_poly b e) v =
          degree_of Reals p v + degree_of Reals q v`
  by (
    gen_tac
    \\ qpat_assum`_ = char_poly _ _`(SUBST1_TAC o SYM)
    \\ DEP_REWRITE_TAC[Q.GEN`s`degree_of_mpoly_mul]
    \\ qexists_tac`support Reals p UNION support Reals q UNION {v}`
    \\ simp_tac(srw_ss())[SUBSET_DEF]
    \\ simp[] )
  \\ `DISJOINT (support Reals p) (support Reals q)`
  by (
    rw[IN_DISJOINT]
    \\ CCONTR_TAC \\ fs[]
    \\ `FINITE (monomials Reals p) ∧ FINITE (monomials Reals q)` by fs[mpoly_def]
    \\ fs[support_degree_of]
    \\ `2 ≤ degree_of Reals (char_poly b e) x` by simp[]
    \\ `degree_of Reals (char_poly b e) x ≤ 1`
    by (
      irule degree_of_char_poly
      \\ metis_tac[SUBSET_FINITE, factorises_FINITE] )
    \\ fs[] )
  \\ `∀m. m IN monomials Reals (mpoly_mul Reals p q) ==>
          mpoly_mul Reals p q m = 1 ∧
          ∃s. m = mono_bag b s ∧ s ∈ e`
  by (
    simp[monomials_char_poly, PULL_EXISTS]
    \\ simp[char_poly_def, mono_bag_poly_def]
    \\ DEP_REWRITE_TAC[GSYM BAG_OF_SET_IMAGE_INJ]
    \\ conj_tac >- metis_tac[mono_bag_inj, SUBSET_DEF]
    \\ simp[BAG_OF_SET]
    \\ metis_tac[] )
  \\ `∀x. rrestrict Reals (p x) = p x /\ rrestrict Reals (q x) = q x`
  by fs[mpoly_def, rrestrict_def, SUBSET_DEF, PULL_EXISTS]
  \\ `∀v1 v2. v1 IN monomials Reals p /\ v2 IN monomials Reals q ==>
              BAG_UNION v1 v2 IN monomials Reals (mpoly_mul Reals p q) /\
              mpoly_mul Reals p q (BAG_UNION v1 v2) = p v1 * q v2`
  by (
    qpat_x_assum`_ = char_poly _ _`(assume_tac o SYM)
    \\ simp[mpoly_mul_BAG_FILTER_cross, PULL_EXISTS]
    \\ ntac 2 gen_tac \\ strip_tac
    \\ simp[Once monomials_def]
    \\ simp[mpoly_mul_BAG_FILTER_cross]
    \\ reverse conj_asm2_tac
    >- (
      simp[BAG_FILTER_BAG_OF_SET]
      \\ qmatch_goalsub_abbrev_tac`BAG_OF_SET s`
      \\ `s = {(v1,v2)}` suffices_by (
        rw[BAG_OF_SET_INSERT_NON_ELEMENT]
        \\ rw[Reals_def] )
      \\ simp[Abbr`s`, Once EXTENSION, FORALL_PROD]
      \\ qx_genl_tac[`w1`,`w2`]
      \\ reverse EQ_TAC >- simp[]
      \\ strip_tac
      \\ pop_assum mp_tac
      \\ simp[FUN_EQ_THM, BAG_UNION]
      \\ fs[IN_DISJOINT, support_def, PULL_EXISTS, BAG_IN, BAG_INN]
      \\ strip_tac
      \\ simp[GSYM FORALL_AND_THM]
      \\ qx_gen_tac`x`
      \\ first_x_assum(qspec_then`x`mp_tac)
      \\ qpat_x_assum`∀x. _ ∨ _`(qspec_then`x`mp_tac)
      \\ `∀x. ~(x >= 1n) <=> x = 0` by simp[] \\ simp[]
      \\ Cases_on`v1 x = 0 ∧ w1 x = 0` \\ simp[]
      \\ Cases_on`v2 x = 0 ∧ w2 x = 0` \\ simp[]
      \\ metis_tac[] )
    \\ simp[]
    \\ simp[Reals_def, rrestrict_def]
    \\ fs[monomials_def, Reals_def, rrestrict_def] )
  \\ `∃r. !m. p m <> 0 ==> p m = r`
  by (
    Cases_on`monomials Reals p = {}`
    >- fs[empty_monomials, FUN_EQ_THM, Reals_def]
    \\ pop_assum mp_tac \\ rw[GSYM MEMBER_NOT_EMPTY]
    \\ qexists_tac`p x` \\ rw[]
    \\ `m IN monomials Reals p` by simp[monomials_def, Reals_def]
    \\ Cases_on`monomials Reals q = {}`
    >- fs[empty_monomials, FUN_EQ_THM, Reals_def]
    \\ pop_assum mp_tac \\ rw[GSYM MEMBER_NOT_EMPTY]
    \\ `p m * q x' = p x * q x'` by metis_tac[]
    \\ `p m * q x' = 1` by metis_tac[]
    \\ Cases_on`q x' = 0` \\ fs[] )
  \\ `∀m. q m <> 0 ==> q m = realinv r`
  by (
    rw[]
    \\ Cases_on`monomials Reals p = {}`
    >- fs[empty_monomials, FUN_EQ_THM, Reals_def]
    \\ pop_assum mp_tac \\ rw[GSYM MEMBER_NOT_EMPTY]
    \\ `m IN monomials Reals q` by simp[monomials_def, Reals_def]
    \\ `p x * q m = 1` by metis_tac[]
    \\ drule realTheory.REAL_RINV_UNIQ
    \\ Cases_on`p x = 0` \\ fs[monomials_def, Reals_def] )
  \\ qexists_tac`r`
  \\ qabbrev_tac`c = { x | x ∈ b ∧ ¬DISJOINT x (support Reals p) }`
  \\ qexists_tac`c`
  \\ reverse conj_tac >- simp[SUBSET_DEF, Abbr`c`]
  \\ `∀x. x ∈ b ∧ ¬DISJOINT x (support Reals p) ==>
                  DISJOINT x (support Reals q)`
  by (
    rw[]
    \\ fs[IN_DISJOINT]
    \\ CCONTR_TAC \\ fs[]
    \\ ntac 2 (qpat_x_assum`_ ∈ support _ _`mp_tac)
    \\ qmatch_goalsub_rename_tac`x1 ∈ support _ p ⇒ x2 ∈ _ ⇒ _`
    \\ Cases_on `x1 = x2` >- metis_tac[]
    \\ simp[support_def] \\ strip_tac
    \\ CCONTR_TAC \\ fs[]
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ qmatch_asmsub_rename_tac`b1 IN monomials _ p`
    \\ qmatch_asmsub_rename_tac`b2 IN monomials _ q`
    \\ `∃s. BAG_UNION b1 b2 = mono_bag b s ∧ s ∈ e` by metis_tac[]
    \\ fs[mono_bag_def]
    \\ qmatch_asmsub_abbrev_tac`BAG_UNION b1 b2 = BAG_IMAGE pp bb`
    \\ `BAG_IN x1 (BAG_IMAGE pp bb) ∧ BAG_IN x2 (BAG_IMAGE pp bb)`
    by metis_tac[BAG_IN_BAG_UNION]
    \\ `FINITE_BAG bb` by simp[Abbr`bb`, FINITE_BAG_OF_SET]
    \\ fs[BAG_IN_FINITE_BAG_IMAGE, Abbr`pp`] \\ rw[]
    \\ `x partitions w` by fs[factorises_def]
    \\ drule partitions_DISJOINT
    \\ simp[]
    \\ qmatch_asmsub_rename_tac`part y1 s <> part y2 s`
    \\ qexistsl_tac[`part y1 s`, `part y2 s`]
    \\ simp[IN_DISJOINT]
    \\ qexists_tac`s`
    \\ rfs[Abbr`bb`]
    \\ `y1 partitions w ∧ y2 partitions w` by fs[factorises_def]
    \\ metis_tac[in_part, SUBSET_DEF] )
  \\ `∀x. x ∈ b ∧ ¬DISJOINT x (support Reals q) ⇒ DISJOINT x (support Reals p)`
  by ( rw[] \\ metis_tac[] )
  \\ `∀x. x ∈ b ∧ DISJOINT x (support Reals p) ∧ DISJOINT x (support Reals q) ⇒ F`
  by (
    rpt strip_tac
    \\ rfs[support_char_poly]
    \\ `∃y. y ∈ e` by metis_tac[MEMBER_NOT_EMPTY]
    \\ `part x y ∈ support Reals p ∪ support Reals q`
    by (
      qpat_x_assum`_ = _`(SUBST1_TAC)
      \\ simp[EXISTS_PROD]
      \\ metis_tac[] )
    \\ `x partitions w` by fs[factorises_def]
    \\ `y ∈ w` by fs[SUBSET_DEF]
    \\ `part x y ∈ x` by metis_tac[part_in_partition]
    \\ fs[IN_DISJOINT]
    \\ metis_tac[] )
  \\ `∀x t. x ∈ b ∧ t IN monomials Reals (char_poly b e) ⇒
            ∃!s. s ∈ x ∧ BAG_IN s t`
  by (rpt strip_tac
      \\ irule char_poly_unique_parts
      \\ metis_tac[])
  \\ `∀x t. x ∈ c ∧ t IN monomials Reals p ⇒ ∃!s. s ∈ x ∧ BAG_IN s t`
  by (
    rpt strip_tac
    \\ `x ∈ b` by fs[Abbr`c`]
    \\ `¬DISJOINT x (support Reals p)` by fs[Abbr`c`]
    \\ `DISJOINT x (support Reals q)` by metis_tac[]
    \\ Cases_on`monomials Reals q = {}`
    >- fs[empty_monomials, FUN_EQ_THM, Reals_def]
    \\ pop_assum mp_tac \\ rw[GSYM MEMBER_NOT_EMPTY]
    \\ qmatch_assum_rename_tac`u IN monomials _ q`
    \\ `BAG_UNION t u IN monomials Reals (mpoly_mul Reals p q)` by metis_tac[]
    \\ `BAG_UNION t u IN monomials Reals (char_poly b e)` by metis_tac[]
    \\ `∃!s. s ∈ x ∧ BAG_IN s (BAG_UNION t u)` by PROVE_TAC[]
    \\ pop_assum mp_tac \\ simp_tac(srw_ss())[EXISTS_UNIQUE_ALT]
    \\ strip_tac
    \\ `¬BAG_IN s u`
    by (
      qhdtm_x_assum`DISJOINT`mp_tac
      \\ simp_tac(srw_ss())[IN_DISJOINT, support_def]
      \\ disch_then(qspec_then`s`mp_tac)
      \\ strip_tac >- metis_tac[]
      \\ first_x_assum(qspec_then`SET_OF_BAG u`mp_tac)
      \\ simp[] \\ metis_tac[])
    \\ metis_tac[])
  \\ simp[Once FUN_EQ_THM]
  \\ simp[ffs_poly_def]
  \\ simp[mono_bag_poly_def, BAG_OF_SET]
  \\ gen_tac
  \\ `∀x. x IN c ==> ∃s t. t IN monomials Reals p /\ BAG_IN s t /\ s IN x`
  by (
    rw[Abbr`c`, IN_DISJOINT]
    \\ pop_assum mp_tac
    \\ simp[support_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `∀m. m IN (IMAGE (mono_bag c) e) ==>
          ?t. t IN monomials Reals (mpoly_mul Reals p q) /\ SUB_BAG m t`
  by (
    rw[PULL_EXISTS]
    \\ qexists_tac`x` \\ simp[]
    \\ irule mono_bag_SUB_BAG
    \\ simp[Abbr`c`, SUBSET_DEF] )
  \\ pop_assum mp_tac \\ simp_tac(srw_ss())[PULL_EXISTS]
  \\ strip_tac
  \\ `x IN monomials Reals p <=> x IN IMAGE (mono_bag c) e`
  suffices_by (
    simp[]
    \\ IF_CASES_TAC
    \\ simp[monomials_def, Reals_def] )
  \\ `c SUBSET b` by simp[SUBSET_DEF, Abbr`c`]
  \\ `FINITE c` by metis_tac[SUBSET_FINITE]
  \\ `PAIR_DISJOINT b` by metis_tac[factors_DISJOINT]
  \\ `PAIR_DISJOINT c` by metis_tac[SUBSET_DEF]
  \\ `∀m. m IN monomials Reals p ==> SET_OF_BAG m ⊆ support Reals p`
  by (
    simp[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `∀m. m IN monomials Reals q ==> SET_OF_BAG m ⊆ support Reals q`
  by (
    simp[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `∀m. m IN monomials Reals p ==> SET_OF_BAG m ⊆ BIGUNION b`
  by (
    rpt strip_tac
    \\ irule SUBSET_TRANS
    \\ qexists_tac`support Reals p`
    \\ conj_tac >- metis_tac[]
    \\ irule SUBSET_TRANS
    \\ qexists_tac`support Reals (char_poly b e)`
    \\ conj_tac
    >- (
      rewrite_tac[SUBSET_DEF]
      \\ metis_tac[EXTENSION, IN_UNION] )
    \\ simp[support_char_poly, SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ qx_genl_tac[`v`,`z`]
    \\ strip_tac
    \\ metis_tac[part_in_partition, factorises_def, SUBSET_DEF] )
  \\ `∀m. m IN monomials Reals q ==> SET_OF_BAG m ⊆ BIGUNION b`
  by (
    rpt strip_tac
    \\ irule SUBSET_TRANS
    \\ qexists_tac`support Reals q`
    \\ conj_tac >- metis_tac[]
    \\ irule SUBSET_TRANS
    \\ qexists_tac`support Reals (char_poly b e)`
    \\ conj_tac
    >- (
      rewrite_tac[SUBSET_DEF]
      \\ metis_tac[EXTENSION, IN_UNION] )
    \\ simp[support_char_poly, SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ qx_genl_tac[`v`,`z`]
    \\ strip_tac
    \\ metis_tac[part_in_partition, factorises_def, SUBSET_DEF] )
  \\ `∀m. m IN monomials Reals p ==> SET_OF_BAG m ⊆ BIGUNION c`
  by (
    simp[Abbr`c`, SUBSET_DEF]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ simp[IN_DISJOINT, support_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `∀m. m IN monomials Reals q ==> SET_OF_BAG m ⊆ BIGUNION (b DIFF c)`
  by (
    simp[Abbr`c`, SUBSET_DEF]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ strip_tac
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ `¬DISJOINT s (support Reals q)` suffices_by metis_tac[]
    \\ simp[IN_DISJOINT, support_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ Cases_on`monomials Reals p = {{||}}`
  >- (
    simp[]
    \\ Cases_on`c = {}` \\ simp[]
    >- metis_tac[MEMBER_NOT_EMPTY]
    \\ pop_assum mp_tac
    \\ simp[Abbr`c`, EXTENSION]
    \\ simp[support_def, IN_DISJOINT] )
  \\ Cases_on`monomials Reals p = {}`
  >- fs[empty_monomials, FUN_EQ_THM, Reals_def]
  \\ `support Reals p <> {}` by (
    strip_tac \\ fs[empty_support]
    \\ ntac 3 (pop_assum mp_tac)
    \\ simp[EXTENSION, SUBSET_DEF]
    \\ metis_tac[] )
  \\ `support Reals p SUBSET BIGUNION c`
  by (
    simp[support_def, SUBSET_DEF, PULL_EXISTS]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[SUBSET_DEF, PULL_EXISTS] )
  \\ `c <> {}`
  by (
    simp[Abbr`c`, EXTENSION]
    \\ simp[IN_DISJOINT]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[SUBSET_DEF, IN_DISJOINT, PULL_EXISTS]
    \\ metis_tac[MEMBER_NOT_EMPTY] )
  \\ Cases_on`{||} IN monomials Reals p`
  >- PROVE_TAC[EXISTS_UNIQUE_THM, BAG_MEMBER_NOT_EMPTY, MEMBER_NOT_EMPTY]
  \\ simp[]
  \\ `∀x. x IN e ==> mono_bag b x IN monomials Reals (mpoly_mul Reals p q)`
  by simp[]
  \\ `∀m. m IN monomials Reals (mpoly_mul Reals p q) ==> ∃mp mq.
          mp IN monomials Reals p /\ mq IN monomials Reals q /\
          m = BAG_UNION mp mq`
  by (
    rpt strip_tac
    \\ qspecl_then[`Reals`,`p`,`q`]mp_tac
         (Q.GENL[`r`,`p1`,`p2`]monomials_mpoly_mul_SUBSET)
    \\ simp_tac(srw_ss())[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
    \\ disch_then drule
    \\ metis_tac[] )
  \\ reverse eq_tac
  >- (
    disch_then(qx_choose_then`s`strip_assume_tac)
    \\ `mono_bag b s IN monomials Reals (mpoly_mul Reals p q)` by metis_tac[]
    \\ `mono_bag c s <= mono_bag b s` by ( irule mono_bag_SUB_BAG \\ simp[] )
    \\ `∃mp mq. mp IN monomials Reals p /\ mq IN monomials Reals q /\
                mono_bag b s = BAG_UNION mp mq` by metis_tac[]
    \\ `x = mp` suffices_by metis_tac[]
    \\ `SET_OF_BAG mq SUBSET BIGUNION (b DIFF c)` by metis_tac[]
    \\ BasicProvers.VAR_EQ_TAC
    \\ `DISJOINT (SET_OF_BAG mp) (SET_OF_BAG mq)`
    by (
      simp[IN_DISJOINT]
      \\ qpat_x_assum`DISJOINT (support _ _) _`mp_tac
      \\ simp[IN_DISJOINT, support_def, PULL_EXISTS]
      \\ metis_tac[] )
    \\ simp[Once FUN_EQ_THM]
    \\ qx_gen_tac`x`
    \\ Cases_on`x IN SET_OF_BAG mp`
    >- (
      `x NOTIN SET_OF_BAG mq` by metis_tac[IN_DISJOINT]
      \\ `~BAG_IN x mq` by fs[]
      \\ `mq x = 0` by fs[BAG_IN, BAG_INN]
      \\ `mono_bag b s x = mp x` by simp[BAG_UNION]
      \\ `BAG_IN x mp` by fs[]
      \\ `x IN BIGUNION c` by metis_tac[SUBSET_DEF]
      \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
      \\ disch_then(qx_choose_then`y`strip_assume_tac)
      \\ `∃!z. z IN y /\ BAG_IN z mp` by PROVE_TAC[]
      \\ simp[mono_bag_def, BAG_IMAGE_DEF, BAG_FILTER_BAG_OF_SET]
      \\ simp[BAG_CARD_BAG_OF_SET]
      \\ qpat_x_assum`_ = mp x`(SUBST1_TAC o SYM)
      \\ simp_tac(srw_ss())[mono_bag_def]
      \\ simp[BAG_IMAGE_DEF, BAG_FILTER_BAG_OF_SET, BAG_CARD_BAG_OF_SET]
      \\ AP_TERM_TAC
      \\ simp[Once EXTENSION]
      \\ qx_gen_tac`n`
      \\ eq_tac >- metis_tac[SUBSET_DEF]
      \\ strip_tac
      \\ simp[]
      \\ `y IN b` by metis_tac[SUBSET_DEF]
      \\ `x IN n` by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
      \\ Cases_on`n = y` \\ simp[]
      \\ `DISJOINT y n` by metis_tac[factors_DISJOINT]
      \\ metis_tac[IN_DISJOINT] )
    \\ `¬BAG_IN x mp` by fs[]
    \\ `mp x = 0` by fs[BAG_IN, BAG_INN]
    \\ Cases_on`mono_bag c s x = 0` \\ simp[]
    \\ `mono_bag c s x <= mono_bag b s x`
    by (
      rfs[SUB_BAG]
      \\ fs[BAG_INN]
      \\ fs[arithmeticTheory.GREATER_EQ] )
    \\ `mono_bag b s x <> 0` by (strip_tac \\ fs[])
    \\ `BAG_IN x (mono_bag b s)` by (
      pop_assum mp_tac \\ simp_tac(srw_ss())[BAG_IN, BAG_INN]
      \\ DECIDE_TAC )
    \\ `BAG_IN x mq` by metis_tac[BAG_IN_BAG_UNION]
    \\ `x IN SET_OF_BAG mq` by fs[]
    \\ `x IN BIGUNION (b DIFF c)` by metis_tac[SUBSET_DEF]
    \\ `BAG_IN x (mono_bag c s)` by fs[BAG_IN, BAG_INN]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[PULL_EXISTS, mono_bag_def]
    \\ rw[]
    \\ reverse(Cases_on`y IN b`) >- metis_tac[SUBSET_DEF]
    \\ qmatch_assum_rename_tac`z NOTIN c`
    \\ `y = z` suffices_by rw[]
    \\ CCONTR_TAC
    \\ `DISJOINT y z` by metis_tac[factors_DISJOINT]
    \\ `part y s IN y` suffices_by metis_tac[IN_DISJOINT]
    \\ irule part_in_partition
    \\ metis_tac[SUBSET_DEF, factorises_def] )
  \\ strip_tac
  \\ Cases_on`monomials Reals q = {}`
  >- fs[empty_monomials, FUN_EQ_THM, Reals_def]
  \\ `∃mq. mq IN monomials Reals q` by metis_tac[MEMBER_NOT_EMPTY]
  \\ qmatch_assum_rename_tac`mp IN monomials Reals p`
  \\ `BAG_UNION mp mq IN monomials Reals (char_poly b e)`
  by metis_tac[]
  \\ pop_assum mp_tac
  \\ simp_tac(srw_ss())[]
  \\ disch_then(qx_choose_then`s`strip_assume_tac)
  \\ qexists_tac`s` \\ simp[]
  \\ `SET_OF_BAG mq SUBSET BIGUNION (b DIFF c)` by metis_tac[]
  \\ `DISJOINT (SET_OF_BAG mp) (SET_OF_BAG mq)`
  by (
    simp[IN_DISJOINT]
    \\ qpat_x_assum`DISJOINT (support _ _) _`mp_tac
    \\ simp[IN_DISJOINT, support_def, PULL_EXISTS]
    \\ metis_tac[] )
  \\ simp[Once FUN_EQ_THM]
  \\ qx_gen_tac`x`
  \\ Cases_on`x IN SET_OF_BAG mp`
  >- (
    `x NOTIN SET_OF_BAG mq` by metis_tac[IN_DISJOINT]
    \\ `~BAG_IN x mq` by fs[]
    \\ `mq x = 0` by fs[BAG_IN, BAG_INN]
    \\ `(BAG_UNION mp mq) x = mp x` by (
      simp_tac(srw_ss())[BAG_UNION] \\ simp[] )
    \\ `BAG_IN x mp` by fs[]
    \\ `x IN BIGUNION c` by metis_tac[SUBSET_DEF]
    \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
    \\ disch_then(qx_choose_then`y`strip_assume_tac)
    \\ `∃!z. z IN y /\ BAG_IN z mp` by PROVE_TAC[]
    \\ simp[mono_bag_def, BAG_IMAGE_DEF, BAG_FILTER_BAG_OF_SET]
    \\ simp[BAG_CARD_BAG_OF_SET]
    \\ qpat_x_assum`_ = mp x`(SUBST1_TAC o SYM)
    \\ qpat_x_assum`BAG_UNION _ _ = _`SUBST1_TAC
    \\ simp_tac(srw_ss())[mono_bag_def]
    \\ simp[BAG_IMAGE_DEF, BAG_FILTER_BAG_OF_SET, BAG_CARD_BAG_OF_SET]
    \\ AP_TERM_TAC
    \\ simp[Once EXTENSION]
    \\ qx_gen_tac`n`
    \\ reverse eq_tac >- metis_tac[SUBSET_DEF]
    \\ strip_tac
    \\ simp[]
    \\ `y IN b` by metis_tac[SUBSET_DEF]
    \\ `x IN n` by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
    \\ Cases_on`n = y` \\ simp[]
    \\ `DISJOINT y n` by metis_tac[factors_DISJOINT]
    \\ metis_tac[IN_DISJOINT] )
  \\ `¬BAG_IN x mp` by fs[]
  \\ `mp x = 0` by fs[BAG_IN, BAG_INN]
  \\ Cases_on`mono_bag c s x = 0` \\ simp[]
  \\ `mono_bag c s <= mono_bag b s`
  by ( irule mono_bag_SUB_BAG \\ simp[] )
  \\ `mono_bag c s x <= mono_bag b s x`
  by (
    rfs[SUB_BAG]
    \\ fs[BAG_INN]
    \\ fs[arithmeticTheory.GREATER_EQ] )
  \\ `mono_bag b s x <> 0` by (strip_tac \\ fs[])
  \\ `BAG_IN x (mono_bag b s)` by (
    pop_assum mp_tac \\ simp_tac(srw_ss())[BAG_IN, BAG_INN]
    \\ DECIDE_TAC )
  \\ `BAG_IN x mq` by metis_tac[BAG_IN_BAG_UNION]
  \\ `x IN SET_OF_BAG mq` by fs[]
  \\ `x IN BIGUNION (b DIFF c)` by metis_tac[SUBSET_DEF]
  \\ `BAG_IN x (mono_bag c s)` by fs[BAG_IN, BAG_INN]
  \\ ntac 2 (pop_assum mp_tac)
  \\ simp[PULL_EXISTS, mono_bag_def]
  \\ rw[]
  \\ reverse(Cases_on`y IN b`) >- metis_tac[SUBSET_DEF]
  \\ qmatch_assum_rename_tac`z NOTIN c`
  \\ `y = z` suffices_by rw[]
  \\ CCONTR_TAC
  \\ `DISJOINT y z` by metis_tac[factors_DISJOINT]
  \\ `part y s IN y` suffices_by metis_tac[IN_DISJOINT]
  \\ irule part_in_partition
  \\ metis_tac[SUBSET_DEF, factorises_def]
QED

Definition ffs_irr_def:
  ffs_irr w b e = { c |
    c <> {} /\ c SUBSET b /\
    { chim w b c s t | (s,t) | s IN e /\ t IN e } = e /\
    !d. d <> {} /\ d PSUBSET c ==>
          { chim w b d s t | (s,t) | s IN e /\ t IN e } <> e }
End

Theorem ffs_irr_partitions:
  FINITE b /\ b factorises w /\ e <> {} /\ e SUBSET w ==>
  ffs_irr w b e partitions b
Proof
  strip_tac
  \\ simp[partitions_PAIR_DISJOINT]
  \\ conj_tac >- simp[ffs_irr_def]
  \\ conj_tac
  >- (
    rw[ffs_irr_def]
    \\ `{chim w b (s INTER t) x y | (x,y) | x IN e /\ y IN e} = e`
    by ( irule chim_closed_INTER \\ simp[] )
    \\ Cases_on`s INTER t = {}` >- simp[DISJOINT_DEF]
    \\ Cases_on`s INTER t PSUBSET t` >- metis_tac[]
    \\ Cases_on`s INTER t PSUBSET s` >- metis_tac[]
    \\ ntac 2 (pop_assum mp_tac)
    \\ simp[PSUBSET_DEF] )
  \\ `{ chim w b b s t | (s,t) | s IN e /\ t IN e } = e`
  by (
    simp[Once EXTENSION]
    \\ rw[EQ_IMP_THM]
    \\ TRY(qexistsl_tac[`x`,`x`])
    \\ DEP_REWRITE_TAC[chim_full]
    \\ fs[SUBSET_DEF] )
  \\ simp[Once EXTENSION, PULL_EXISTS]
  \\ rw[EQ_IMP_THM]
  >- fs[ffs_irr_def, SUBSET_DEF]
  \\ qexists_tac`BIGINTER { c | c SUBSET b /\ x IN c /\ { chim w b c s t | (s,t) | s IN e /\ t IN e} = e}`
  \\ conj_asm1_tac >- simp[]
  \\ qmatch_goalsub_abbrev_tac`cx IN _`
  \\ simp[ffs_irr_def]
  \\ conj_tac >- metis_tac[MEMBER_NOT_EMPTY]
  \\ conj_asm1_tac >- simp[SUBSET_DEF,Abbr`cx`]
  \\ conj_asm1_tac
  >- (
    qunabbrev_tac`cx`
    \\ irule chim_closed_BIGINTER
    \\ simp[]
    \\ conj_tac
    >- (
      irule SUBSET_FINITE
      \\ qexists_tac`POW b`
      \\ simp[SUBSET_DEF, IN_POW] )
    \\ simp[Once EXTENSION]
    \\ qexists_tac`b`
    \\ simp[] )
  \\ rpt strip_tac
  \\ Cases_on`x IN d`
  >- (
    qmatch_asmsub_abbrev_tac`BIGINTER P`
    \\ `d IN P` by ( simp[Abbr`P`] \\ fs[SUBSET_DEF, PSUBSET_DEF] )
    \\ `cx SUBSET d`
    by (
      qunabbrev_tac`cx`
      \\ irule BIGINTER_SUBSET
      \\ qexists_tac`d` \\ simp[] )
    \\ fs[SUBSET_DEF, PSUBSET_DEF]
    \\ metis_tac[EXTENSION] )
  \\ `{chim w b (b DIFF d) s t | (s,t) | s IN e /\ t IN e} = e`
  by (
    qmatch_goalsub_abbrev_tac`xx = _`
    \\ qpat_x_assum`_ = e`(SUBST1_TAC o SYM)
    \\ qunabbrev_tac`xx`
    \\ qmatch_goalsub_abbrev_tac`chim w b bd _ _`
    \\ simp[Once EXTENSION]
    \\ gen_tac \\ rw[EQ_IMP_THM]
    \\ qexistsl_tac[`t`,`s`]
    \\ simp[]
    \\ qunabbrev_tac`bd`
    \\ DEP_REWRITE_TAC[chim_DIFF]
    \\ fs[SUBSET_DEF, PSUBSET_DEF] )
  \\ `{chim w b (cx DIFF d) s t | (s,t) | s IN e /\ t IN e} = e`
  by (
    `cx DIFF d = (b DIFF d) INTER cx`
    by ( simp[SET_EQ_SUBSET] \\ fs[SUBSET_DEF, PSUBSET_DEF] )
    \\ pop_assum SUBST1_TAC
    \\ qmatch_goalsub_abbrev_tac`chim w b bdc _ _`
    \\ qmatch_asmsub_abbrev_tac`bdc = bd INTER _`
    \\ rpt(qpat_x_assum`_ = e`mp_tac)
    \\ simp[EXTENSION]
    \\ rewrite_tac[EQ_IMP_THM]
    \\ simp_tac bool_ss [PULL_EXISTS]
    \\ rpt strip_tac
    >- (
      qunabbrev_tac`bdc`
      \\ DEP_REWRITE_TAC[chim_INTER]
      \\ conj_tac >- ( unabbrev_all_tac \\ fs[SUBSET_DEF] )
      \\ metis_tac[] )
    \\ qmatch_assum_rename_tac`z IN e`
    \\ qexistsl_tac[`z`,`z`]
    \\ DEP_REWRITE_TAC[chim_same]
    \\ fs[SUBSET_DEF, Abbr`bdc`] )
  \\ qmatch_asmsub_abbrev_tac`BIGINTER P`
  \\ `(cx DIFF d) IN P` by ( simp[Abbr`P`] \\ fs[SUBSET_DEF, PSUBSET_DEF] )
  \\ `cx SUBSET cx DIFF d`
  by (
    qunabbrev_tac`cx`
    \\ irule BIGINTER_SUBSET
    \\ metis_tac[SUBSET_REFL] )
  \\ fs[SUBSET_DEF, PSUBSET_DEF]
  \\ metis_tac[MEMBER_NOT_EMPTY]
QED

Theorem char_poly_ffs_poly_irr:
  FINITE w /\ b factorises w /\ e <> {} /\ e SUBSET w /\ POW w SUBSET s ==>
  char_poly b e = GBAG (mpoly_ring Reals s).prod
    (BAG_IMAGE (flip ffs_poly e) (BAG_OF_SET (ffs_irr w b e)))
Proof
  strip_tac
  \\ `FINITE b /\ FINITE e` by metis_tac[factorises_FINITE, SUBSET_FINITE]
  \\ `ffs_irr w b e partitions b` by metis_tac[ffs_irr_partitions]
  \\ `FINITE (ffs_irr w b e)` by metis_tac[partitions_FINITE]
  \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
  \\ simp[]
  \\ `BAG_OF_SET (ffs_irr w b e) =
      LIST_TO_BAG (SET_TO_LIST (ffs_irr w b e))`
  by simp[LIST_TO_BAG_SET_TO_LIST]
  \\ pop_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`LIST_TO_BAG ls`
  \\ `b = BIGUNION (set ls)`
  by (
    simp[Abbr`ls`]
    \\ DEP_REWRITE_TAC[listTheory.SET_TO_LIST_INV]
    \\ metis_tac[partitions_covers] )
  \\ pop_assum SUBST1_TAC
  \\ `set ls SUBSET ffs_irr w b e`
  by (
    simp[Abbr`ls`]
    \\ DEP_REWRITE_TAC[listTheory.SET_TO_LIST_INV]
    \\ simp[] )
  \\ pop_assum mp_tac
  \\ `ALL_DISTINCT ls` by simp[Abbr`ls`]
  \\ pop_assum mp_tac
  \\ qid_spec_tac`ls`
  \\ qunabbrev_tac`ls`
  \\ Induct >- (
    rw[]
    \\ rw[ffs_poly_def, mono_bag_poly_def, mpoly_ring_def, FUN_EQ_THM]
    \\ rw[BAG_OF_SET, mpoly_one_def, Reals_def]
    \\ metis_tac[MEMBER_NOT_EMPTY] )
  \\ rw[] \\ fs[]
  \\ `DISJOINT h (BIGUNION (set ls))`
  by (
    simp[IN_DISJOINT]
    \\ qx_gen_tac`v`
    \\ strip_tac
    \\ fs[SUBSET_DEF]
    \\ metis_tac[IN_DISJOINT, partitions_DISJOINT] )
  \\ `e = { chim w b h s t | (s,t) | s IN e /\ t IN e }`
  by fs[ffs_irr_def]
  \\ qmatch_goalsub_abbrev_tac`_ = rhs`
  \\ `e = IMAGE (λ(s,t). chim w b h s t) (e × e)`
  by (
    qmatch_goalsub_abbrev_tac`_ = rhs2`
    \\ qpat_x_assum`e = _`SUBST1_TAC
    \\ simp[Abbr`rhs2`]
    \\ simp[Once EXTENSION, EXISTS_PROD] )
  \\ qpat_x_assum`e = _`SUBST1_TAC
  \\ DEP_REWRITE_TAC[ffs_poly_union_chim_mul]
  \\ qpat_x_assum`e = _`kall_tac
  \\ simp[]
  \\ conj_tac
  >- (
    fs[partitions_thm, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ simp[Abbr`rhs`]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_asm1_tac >- (
    `Ring (mpoly_ring Reals s)` by simp[]
    \\ metis_tac[Ring_def] )
  \\ simp[PULL_EXISTS, SUBSET_DEF]
  \\ qmatch_goalsub_abbrev_tac`mpoly_mul _ _ rr`
  \\ simp[mpoly_ring_def]
  \\ simp[support_ffs_poly]
  \\ fs[SUBSET_DEF, PULL_EXISTS, containerTheory.IN_LIST_TO_BAG]
  \\ `!x. x IN ffs_irr w b e ==> x SUBSET b` by metis_tac[partitions_thm]
  \\ rw[]
  \\ first_x_assum irule
  \\ simp[IN_POW]
  \\ qmatch_goalsub_rename_tac`part v z`
  \\ `v IN b` by metis_tac[SUBSET_DEF]
  \\ `v partitions w` by metis_tac[factorises_def]
  \\ `part v z IN v` by metis_tac[part_in_partition]
  \\ metis_tac[partitions_thm]
QED

Theorem support_cmul_Reals:
  mpoly Reals p /\ c <> 0 ==>
  support Reals ($* c o p) = support Reals p
Proof
  strip_tac
  \\ `$* c = Reals.prod.op c` by simp[Reals_def]
  \\ pop_assum SUBST1_TAC
  \\ irule support_cmul
  \\ simp[]
  \\ simp[Reals_def]
QED

Theorem degree_of_ffs_poly:
  FINITE c /\ FINITE e /\ PAIR_DISJOINT c /\
  (!a. a IN c ==> a partitions w) /\ e SUBSET w
  ==>
  degree_of Reals (ffs_poly c e) v <= 1
Proof
  rw[degree_of_def]
  \\ rw[GSYM IMAGE_COMPOSE]
  \\ rw[combinTheory.o_DEF]
  \\ rw[mono_bag_def, BAG_IMAGE_DEF]
  \\ rw[BAG_FILTER_BAG_OF_SET]
  \\ rw[BAG_CARD_BAG_OF_SET]
  \\ qmatch_goalsub_abbrev_tac`MAX_SET s`
  \\ Cases_on`s = {}` \\ simp[]
  \\ `FINITE s` by simp[Abbr`s`]
  \\ `MAX_SET s IN s` by metis_tac[MAX_SET_DEF]
  \\ `∀x. x IN s ==> x <= 1` suffices_by metis_tac[]
  \\ rw[Abbr`s`]
  \\ qmatch_assum_rename_tac`s IN e`
  \\ reverse(Cases_on`?a. a IN c /\ part a s = v`)
  >- (
    qmatch_goalsub_abbrev_tac`CARD z`
    \\ `z = {}` suffices_by simp[]
    \\ simp[Abbr`z`, Once EXTENSION]
    \\ metis_tac[] )
  \\ fs[]
  \\ Cases_on`∃b. b IN c /\ b <> a /\ part b s = v`
  >- (
    fs[]
    \\ `DISJOINT a b` by metis_tac[]
    \\ `s IN w` by metis_tac[SUBSET_DEF]
    \\ metis_tac[part_in_partition, IN_DISJOINT])
  \\ qmatch_goalsub_abbrev_tac`CARD z`
  \\ `z = {a}` suffices_by simp[]
  \\ simp[Abbr`z`, Once EXTENSION]
  \\ metis_tac[]
QED

Theorem ffs_poly_irreducible:
  FINITE w /\ b factorises w /\ e <> {} /\ e SUBSET w /\
  c IN ffs_irr w b e ==>
  !p q. mpoly Reals p /\ mpoly Reals q /\
        support Reals p ⊆ POW w /\
        support Reals q ⊆ POW w /\
        ffs_poly c e = mpoly_mul Reals p q
    ==> support Reals p = {} \/ support Reals q = {}
Proof
  rw[]
  \\ CCONTR_TAC \\ fs[]
  \\ `FINITE b` by metis_tac[factorises_FINITE]
  \\ `ffs_irr w b e SUBSET POW b`
  by simp[ffs_irr_def, SUBSET_DEF, IN_POW]
  \\ `FINITE (ffs_irr w b e)` by metis_tac[SUBSET_FINITE, FINITE_POW]
  \\ `FINITE e` by metis_tac[SUBSET_FINITE]
  \\ `Ring (mpoly_ring Reals (POW w))` by simp[]
  \\ `AbelianMonoid (mpoly_ring Reals (POW w)).prod` by metis_tac[Ring_def]
  \\ `FINITE (support Reals p) /\ FINITE (support Reals q)`
  by metis_tac[SUBSET_FINITE, FINITE_POW]
  \\ `!p q. ffs_poly c e = mpoly_mul Reals p q /\
            mpoly Reals p /\ mpoly Reals q /\
            support Reals p SUBSET POW w /\
            support Reals q SUBSET POW w ==>
            ∃qr. mpoly_mul Reals p qr = char_poly b e /\
                 mpoly Reals qr /\ support Reals qr SUBSET POW w`
  by (
    qx_genl_tac[`p0`,`p1`]
    \\ strip_tac
    \\ DEP_REWRITE_TAC[Q.SPEC`POW w`(Q.GEN`s`char_poly_ffs_poly_irr)]
    \\ simp[]
    \\ `ffs_irr w b e = c INSERT (ffs_irr w b e DELETE c)`
    by metis_tac[INSERT_DELETE]
    \\ qmatch_asmsub_abbrev_tac`c INSERT rest`
    \\ `c NOTIN rest` by simp[Abbr`rest`]
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_INSERT]
    \\ simp[]
    \\ conj_asm1_tac >- metis_tac[FINITE_INSERT]
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ simp[]
    \\ conj_tac
    >- (
      simp[mpoly_ring_def, SUBSET_DEF, PULL_EXISTS]
      \\ simp[support_ffs_poly, PULL_EXISTS, Abbr`rest`]
      \\ imp_res_tac mpoly_def
      \\ simp[mpoly_mpoly_mul]
      \\ fs[SUBSET_DEF, PULL_EXISTS, IN_POW]
      \\ rw[]
      >- (
        qmatch_assum_rename_tac`s IN part v a`
        \\ qmatch_assum_rename_tac`v IN f`
        \\ `v IN b` by metis_tac[]
        \\ `v partitions w` by metis_tac[factorises_def]
        \\ metis_tac[SUBSET_DEF, part_in_partition, partitions_thm] )
      \\ `support Reals (mpoly_mul Reals p q) SUBSET
          support Reals p UNION support Reals q`
      by ( irule support_mpoly_mul_SUBSET \\ simp[] )
      \\ fs[SUBSET_DEF]
      \\ metis_tac[] )
    \\ qmatch_goalsub_abbrev_tac`_.op _ qr`
    \\ simp[mpoly_ring_def]
    \\ `qr IN (mpoly_ring Reals (POW w)).prod.carrier`
    by (
      qunabbrev_tac`qr`
      \\ irule GBAG_in_carrier
      \\ simp[SUBSET_DEF, PULL_EXISTS]
      \\ simp[mpoly_ring_def, support_ffs_poly]
      \\ fs[SUBSET_DEF, PULL_EXISTS, IN_POW]
      \\ rw[]
      \\ qmatch_assum_rename_tac`s IN part v a`
      \\ qmatch_assum_rename_tac`v IN f`
      \\ `v IN b` by metis_tac[]
      \\ `v partitions w` by metis_tac[factorises_def]
      \\ metis_tac[SUBSET_DEF, part_in_partition, partitions_thm] )
    \\ DEP_REWRITE_TAC[mpoly_mul_assoc]
    \\ pop_assum mp_tac
    \\ simp[mpoly_ring_def] \\ strip_tac
    \\ conj_asm1_tac >- metis_tac[mpoly_def]
    \\ qexists_tac`mpoly_mul Reals p1 qr`
    \\ simp[]
    \\ conj_tac >- metis_tac[mpoly_mpoly_mul, RingReals]
    \\ metis_tac[RingReals, support_mpoly_mul_SUBSET,
                 UNION_SUBSET, SUBSET_TRANS])
  \\ `mpoly_mul Reals q p = mpoly_mul Reals p q`
  by metis_tac[RingReals, mpoly_def, mpoly_mul_comm]
  \\ `∃rp cp. p = $* rp o ffs_poly cp e ∧ cp ⊆ b`
  by (
    irule divides_char_poly_multiple_ffs_poly
    \\ metis_tac[SUBSET_FINITE, FINITE_POW] )
  \\ `∃rq cq. q = $* rq o ffs_poly cq e ∧ cq ⊆ b`
  by (
    irule divides_char_poly_multiple_ffs_poly
    \\ metis_tac[SUBSET_FINITE, FINITE_POW] )
  \\ `p <> K Reals.sum.id /\ q <> K Reals.sum.id`
  by (
    conj_tac \\ strip_tac \\ fs[combinTheory.o_DEF]
    >| [`support Reals p = {}` by metis_tac[support_zero],
        `support Reals q = {}` by metis_tac[support_zero]]
    \\ gs[])
  \\ `rp <> 0 /\ rq <> 0`
  by (
    conj_tac \\ strip_tac \\ fs[combinTheory.o_DEF, Reals_def, FUN_EQ_THM]
    \\ metis_tac[])
  \\ `support Reals p = support Reals (ffs_poly cp e)`
  by ( simp[] \\ DEP_REWRITE_TAC[support_cmul_Reals] \\ simp[] )
  \\ `support Reals q = support Reals (ffs_poly cq e)`
  by ( simp[] \\ DEP_REWRITE_TAC[support_cmul_Reals] \\ simp[] )
  \\ Cases_on`cp = {}` >- fs[support_ffs_poly, IMAGE_EQ_SING]
  \\ Cases_on`cq = {}` >- fs[support_ffs_poly, IMAGE_EQ_SING]
  \\ `DISJOINT cp cq`
  by (
    simp[IN_DISJOINT]
    \\ CCONTR_TAC \\ fs[]
    \\ `∃s. s IN e` by metis_tac[MEMBER_NOT_EMPTY]
    \\ `part x s IN support Reals (ffs_poly cp e) ∧
        part x s IN support Reals (ffs_poly cq e)`
    by (
      simp[support_ffs_poly, PULL_EXISTS]
      \\ metis_tac[] )
    \\ `degree_of Reals (ffs_poly c e) (part x s) >= 2`
    by (
      simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`s`degree_of_mpoly_mul]
      \\ conj_tac
      >- (
        qexists_tac`support Reals p ∪ support Reals q`
        \\ simp[]
        \\ DEP_REWRITE_TAC[support_cmul_Reals]
        \\ simp[]
        \\ metis_tac[])
      \\ qpat_x_assum`p = _`(assume_tac o SYM)
      \\ qpat_x_assum`q = _`(assume_tac o SYM)
      \\ qpat_x_assum`support Reals p = _`(assume_tac o SYM)
      \\ qpat_x_assum`support Reals q = _`(assume_tac o SYM)
      \\ gs[]
      \\ imp_res_tac mpoly_def
      \\ imp_res_tac support_degree_of
      \\ simp[] )
    \\ `degree_of Reals (ffs_poly c e) (part x s) <= 1` suffices_by DECIDE_TAC
    \\ irule degree_of_ffs_poly
    \\ `c SUBSET b` by metis_tac[IN_POW, SUBSET_DEF]
    \\ conj_tac >- metis_tac[factors_DISJOINT, SUBSET_DEF]
    \\ simp[]
    \\ conj_tac >- metis_tac[SUBSET_FINITE]
    \\ metis_tac[factorises_def, SUBSET_DEF] )
  \\ `cp UNION cq = c`
  by (
    `support Reals (ffs_poly c e) =
     support Reals p UNION support Reals q`
    by (
      qpat_x_assum`ffs_poly c e = _`SUBST1_TAC
      \\ irule support_mpoly_mul
      \\ simp[] )
    \\ `∃s. s IN e` by metis_tac[MEMBER_NOT_EMPTY]
    \\ irule EQ_SYM
    \\ simp[Once EXTENSION]
    \\ qx_gen_tac`x`
    \\ `c SUBSET b` by metis_tac[SUBSET_DEF, IN_POW]
    \\ reverse(Cases_on`x IN b`) >- metis_tac[SUBSET_DEF]
    \\ irule EQ_TRANS
    \\ qexists_tac`part x s IN support Reals (ffs_poly c e)`
    \\ conj_tac
    >- (
      simp_tac(srw_ss())[support_ffs_poly, PULL_EXISTS]
      \\ eq_tac >- metis_tac[]
      \\ disch_then(qx_choosel_then[`y`,`z`]strip_assume_tac)
      \\ `part x s IN x /\ part z y IN z`
      by metis_tac[part_in_partition, SUBSET_DEF, factorises_def]
      \\ PROVE_TAC[factors_DISJOINT, SUBSET_DEF, IN_DISJOINT] )
    \\ simp[support_ffs_poly, PULL_EXISTS]
    \\ reverse(rw[EQ_IMP_THM])
    >- metis_tac[]
    >- metis_tac[]
    \\ qmatch_assum_rename_tac`part x s = part y z`
    \\ `part x s IN x /\ part y z IN y`
    by metis_tac[part_in_partition, SUBSET_DEF, factorises_def]
    \\ `s IN part x s /\ z IN part y z`
    by metis_tac[in_part, SUBSET_DEF, factorises_def]
    \\ metis_tac[part_unique, factors_DISJOINT,
                 SUBSET_DEF, IN_DISJOINT, factorises_def] )
  \\ drule_then drule ffs_poly_union_chim_mul
  \\ disch_then (drule_then drule)
  \\ disch_then (first_assum o mp_then (Pat`DISJOINT`)mp_tac)
  \\ impl_tac >- simp[]
  \\ strip_tac
  \\ `ffs_poly c e = Reals.prod.op rp o Reals.prod.op rq o mpoly_mul Reals
        (ffs_poly cp e) (ffs_poly cq e)`
  by (
    qpat_assum`ffs_poly c _ = _`SUBST1_TAC
    \\ qpat_assum`p = _`SUBST1_TAC
    \\ qpat_assum`q = _`SUBST1_TAC
    \\ `$* rq = Reals.prod.op rq /\ $* rp = Reals.prod.op rp`
    by simp[Reals_def]
    \\ pop_assum SUBST1_TAC
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[mpoly_mul_cmul]
    \\ conj_tac >- fs[Reals_def]
    \\ DEP_ONCE_REWRITE_TAC[mpoly_mul_comm]
    \\ conj_tac >- (
      conj_tac >- fs[]
      \\ conj_tac >- fs[]
      \\ DEP_REWRITE_TAC[monomials_cmul]
      \\ fs[]
      \\ simp[Reals_def] )
    \\ DEP_REWRITE_TAC[mpoly_mul_cmul]
    \\ conj_tac >- fs[Reals_def]
    \\ AP_TERM_TAC \\ AP_TERM_TAC
    \\ irule mpoly_mul_comm
    \\ fs[] )
  \\ pop_assum mp_tac
  \\ qpat_assum`_ = mpoly_mul _ _ _`(SUBST1_TAC o SYM)
  \\ qpat_assum`_ = c`(SUBST1_TAC)
  \\ qmatch_goalsub_abbrev_tac`_ o ffs_poly c ee`
  \\ strip_tac
  \\ `mpoly Reals (ffs_poly cp e) /\ mpoly Reals (ffs_poly cq e)`
  by simp[mpoly_def]
  \\ `mpoly Reals (ffs_poly c ee)`
  by (
    gs[]
    \\ irule mpoly_mpoly_mul
    \\ fs[mpoly_def] )
  \\ `monos c e = monos c ee`
  by (
    simp[monos_def]
    \\ first_assum(mp_tac o Q.AP_TERM`monomials Reals`)
    \\ DEP_REWRITE_TAC[monomials_cmul]
    \\ conj_tac
    >- (
      simp[]
      \\ fs[Reals_def]
      \\ fs[GSYM Reals_def]
      \\ `$* rq = Reals.prod.op rq` by simp[Reals_def]
      \\ pop_assum SUBST1_TAC
      \\ irule mpoly_cmul
      \\ simp[]
      \\ simp[Reals_def] )
    \\ simp[monomials_ffs_poly]
    \\ simp[Once EXTENSION]
    \\ strip_tac
    \\ simp[Once EXTENSION, mono_def]
    \\ simp[FUN_EQ_THM, mono_bag_poly_sing]
    \\ fs[FUN_EQ_THM]
    \\ metis_tac[] )
  \\ `ee = e` suffices_by (
    qpat_x_assum`c IN _`mp_tac
    \\ simp[ffs_irr_def]
    \\ rpt strip_tac
    \\ first_x_assum(qspec_then`cp`mp_tac)
    \\ impl_tac >- (
      simp[PSUBSET_DEF]
      \\ qpat_x_assum`_ = c`(SUBST1_TAC o SYM)
      \\ simp[]
      \\ simp[Once EXTENSION]
      \\ metis_tac[IN_DISJOINT, MEMBER_NOT_EMPTY] )
    \\ `ee = {chim w b cp s t | s IN e /\ t IN e}`
    by simp[Abbr`ee`, Once EXTENSION, EXISTS_PROD]
    \\ fs[] )
  \\ simp[SET_EQ_SUBSET]
  \\ reverse conj_tac
  >- (
    simp[Abbr`ee`, SUBSET_DEF, EXISTS_PROD]
    \\ qx_gen_tac `x` \\ strip_tac
    \\ qexistsl_tac[`x`,`x`]
    \\ DEP_REWRITE_TAC[chim_same]
    \\ simp[]
    \\ metis_tac[SUBSET_DEF] )
  \\ simp[SUBSET_DEF, Abbr`ee`, PULL_EXISTS, FORALL_PROD]
  \\ qx_genl_tac[`s`,`t`]
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac`s2 IN e`
  \\ qmatch_asmsub_abbrev_tac`monos c e = monos c ee`
  \\ `s2 IN ee`
  by ( simp[Abbr`ee`, EXISTS_PROD] \\ metis_tac[] )
  \\ `mono c s2 IN monos c ee` by simp[monos_def]
  \\ `mono c s2 IN monos c e` by metis_tac[]
  \\ pop_assum mp_tac
  \\ simp_tac(srw_ss())[monos_def]
  \\ disch_then(qx_choose_then`s3`strip_assume_tac)
  \\ qhdtm_x_assum`mono`mp_tac
  \\ simp[mono_def]
  \\ simp[mono_bag_def]
  \\ DEP_REWRITE_TAC[GSYM BAG_OF_SET_IMAGE_INJ]
  \\ simp[]
  \\ conj_tac
  >- (
    `c SUBSET b` by metis_tac[SUBSET_DEF, IN_POW]
    \\ `PAIR_DISJOINT b` by metis_tac[factors_DISJOINT]
    \\ `PAIR_DISJOINT c` by metis_tac[SUBSET_DEF]
    \\ `∀x. x IN c ==> x partitions w` by metis_tac[factorises_def, SUBSET_DEF]
    \\ `s2 IN w`
    by ( simp[Abbr`s2`] \\ metis_tac[chim_thm, SUBSET_DEF] )
    \\ rpt strip_tac \\ CCONTR_TAC
    \\ `DISJOINT x y` by metis_tac[]
    >- (
      `part y s2 IN y` by metis_tac[part_in_partition]
      \\ `part x s2 IN x` by metis_tac[part_in_partition]
      \\ metis_tac[IN_DISJOINT] )
    \\ PROVE_TAC[part_in_partition, SUBSET_DEF, IN_DISJOINT] )
  \\ simp[]
  \\ strip_tac
  \\ `∀x. x IN (b DIFF cp) ==> part x s2 = part x t`
  by (
    rpt strip_tac
    \\ qunabbrev_tac`s2`
    \\ `x IN b` by fs[]
    \\ `x NOTIN cp` by fs[]
    \\ `s IN w /\ t IN w` by metis_tac[SUBSET_DEF]
    \\ simp[chim_thm] )
  \\ `∀x. x IN b DIFF c ==> x IN b DIFF cp`
  by metis_tac[EXTENSION, IN_UNION, IN_DIFF]
  \\ `∀x. x IN c ==> part x s2 = part x s3`
  by (
    rpt strip_tac
    \\ qhdtm_x_assum`IMAGE`mp_tac
    \\ simp[Once EXTENSION]
    \\ disch_then(qspec_then`part x s2`mp_tac)
    \\ simp_tac std_ss [EQ_IMP_THM, PULL_EXISTS]
    \\ strip_tac
    \\ `∃y. part x s2 = part y s3 ∧ y IN c` by metis_tac[]
    \\ `c SUBSET b` by metis_tac[SUBSET_DEF, IN_POW]
    \\ `PAIR_DISJOINT b` by metis_tac[factors_DISJOINT]
    \\ `PAIR_DISJOINT c` by metis_tac[SUBSET_DEF]
    \\ `∀x. x IN c ==> x partitions w` by metis_tac[factorises_def, SUBSET_DEF]
    \\ `s3 IN w` by metis_tac[SUBSET_DEF]
    \\ Cases_on`x = y` >- metis_tac[]
    \\ `DISJOINT x y` by metis_tac[]
    \\ `part y s3 IN y` by metis_tac[part_in_partition]
    \\ `part x s3 IN x` by metis_tac[part_in_partition]
    \\ `s2 IN w` by ( simp[Abbr`s2`] \\ metis_tac[chim_thm, SUBSET_DEF] )
    \\ `part y s2 IN y` by metis_tac[part_in_partition]
    \\ `part x s2 IN x` by metis_tac[part_in_partition]
    \\ metis_tac[IN_DISJOINT] )
  \\ `s2 = chim w b c s3 t`
  by (
    DEP_REWRITE_TAC[factorises_distinguish]
    \\ conj_tac
    >- (
      simp[]
      \\ `s2 IN w` by ( simp[Abbr`s2`] \\ metis_tac[chim_thm, SUBSET_DEF] )
      \\ metis_tac[chim_thm, SUBSET_DEF] )
    \\ `t IN w /\ s3 IN w` by metis_tac[SUBSET_DEF]
    \\ simp[chim_thm] \\ fs[]
    \\ rpt strip_tac \\ metis_tac[] )
  \\ qpat_x_assum`c IN _`mp_tac
  \\ simp_tac(srw_ss())[ffs_irr_def]
  \\ strip_tac
  \\ qpat_x_assum`_ = e`(SUBST1_TAC o SYM)
  \\ simp[]
  \\ metis_tac[]
QED

Theorem support_ffs_poly_SUBSET_POW:
  b factorises w /\ e SUBSET w /\ c SUBSET b ==>
  support Reals (ffs_poly c e) SUBSET POW w
Proof
  rw[support_ffs_poly, SUBSET_DEF] \\ fs[]
  \\ rw[IN_POW]
  \\ metis_tac[part_in_partition, factorises_def, partitions_thm]
QED

Theorem support_char_poly_SUBSET_POW:
  FINITE b /\ b factorises w /\ FINITE e /\ e SUBSET w ==>
  support Reals (char_poly b e) SUBSET POW w
Proof
  strip_tac
  \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
  \\ simp[]
  \\ irule support_ffs_poly_SUBSET_POW
  \\ metis_tac[SUBSET_REFL]
QED

Theorem ffs_poly_eq_zero:
  ffs_poly c e = K 0 <=> e = {}
Proof
  rw[ffs_poly_def, Once FUN_EQ_THM, mono_bag_poly_def, BAG_OF_SET]
  \\ rw[EQ_IMP_THM]
  \\ CCONTR_TAC
  \\ fs[GSYM MEMBER_NOT_EMPTY]
  \\ first_x_assum(qspec_then`mono_bag c x`mp_tac)
  \\ rw[] \\ metis_tac[]
QED

Theorem constant_mpoly_invertible:
  Ring r /\ mpoly r p /\ monomials r p = {{||}} /\ Unit r (p {||}) ==>
  mpoly_mul r p (one_mono r {||} (Inv r (p {||}))) =
  mpoly_one r
Proof
  rw[]
  \\ rw[mpoly_mul_BAG_FILTER_cross, Once FUN_EQ_THM]
  \\ qmatch_goalsub_abbrev_tac`_ × monomials r om`
  \\ `mpoly r om`
  by (
    qunabbrev_tac`om`
    \\ irule mpoly_one_mono
    \\ simp[ringUnitTheory.ring_unit_inv_element] )
  \\ imp_res_tac mpoly_def
  \\ simp[rrestrict_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[Abbr`om`,monomials_one_mono]
  \\ simp[ringUnitTheory.ring_unit_inv_element]
  \\ rw[]
  >- (
    rw[mpoly_one_def]
    \\ metis_tac[ringUnitTheory.ring_unit_inv_nonzero] )
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
  \\ rw[mpoly_one_def]
  \\ rw[one_mono_def]
  \\ irule ringUnitTheory.ring_unit_rinv
  \\ simp[]
QED

Theorem conditionally_orthogonal_imp_char_poly_factors:
  FINITE w /\ conditionally_orthogonal w b xs ys zs ⇒
  ∀x y z.
    x IN xs /\ y IN ys /\ z IN zs ==>
    mpoly_mul Reals (char_poly b z) (char_poly b (x INTER y INTER z)) =
    mpoly_mul Reals (char_poly b (x INTER z)) (char_poly b (y INTER z))
Proof
  rw[conditionally_orthogonal_def]
  \\ qabbrev_tac`c = subpart_history w b (restrict_partition xs z)`
  \\ `z SUBSET w` by metis_tac[partitions_thm]
  \\ `is_subpartition w (restrict_partition xs z)`
  by ( irule is_subpartition_restrict \\ simp[] )
  \\ `is_subpartition w (restrict_partition ys z)`
  by ( irule is_subpartition_restrict \\ simp[] )
  \\ `generates_subpartition w b c (restrict_partition xs z)`
  by metis_tac[subpart_history_thm]
  \\ `generates_subpartition w b
       (subpart_history w b (restrict_partition ys z))
       (restrict_partition ys z)`
  by metis_tac[subpart_history_thm]
  \\ `subpart_domain w (restrict_partition xs z) = z`
  by metis_tac[subpart_domain_restrict]
  \\ `subpart_domain w (restrict_partition ys z) = z`
  by metis_tac[subpart_domain_restrict]
  \\ `IMAGE (λ(s,t). chim w b c s t) (z × z) = z`
  by (
    fs[generates_subpartition_common_refinement_refines]
    \\ fs[Once EXTENSION, EXISTS_PROD] )
  \\ `c SUBSET b` by metis_tac[subpart_history_SUBSET_factorisation]
  \\ `IMAGE (λ(s,t). chim w b (b DIFF c) s t) (z × z) = z`
  by (
    qmatch_goalsub_abbrev_tac`chim w b bc _ _`
    \\ fs[Once EXTENSION, EXISTS_PROD]
    \\ `bc SUBSET b` by simp[Abbr`bc`, SUBSET_DEF]
    \\ reverse(rw[EQ_IMP_THM])
    >- (
      qmatch_assum_rename_tac`s IN z`
      \\ qexistsl_tac[`s`,`s`]
      \\ DEP_REWRITE_TAC[chim_same]
      \\ metis_tac[SUBSET_DEF] )
    \\ qmatch_goalsub_rename_tac`chim w b bc p q`
    \\ first_x_assum(qspec_then`chim w b c q p`mp_tac)
    \\ rw[EQ_IMP_THM]
    \\ qunabbrev_tac`bc`
    \\ DEP_REWRITE_TAC[chim_DIFF]
    \\ metis_tac[SUBSET_DEF] )
  \\ qmatch_asmsub_abbrev_tac`generates_subpartition w b d _`
  \\ `d SUBSET b DIFF c`
  by (
    imp_res_tac subpart_history_SUBSET_factorisation
    \\ fs[SUBSET_DEF] \\ simp[Abbr`c`]
    \\ metis_tac[IN_DISJOINT] )
  \\ `restrict_partition (common_refinement w d) z refines (restrict_partition ys z)`
  by metis_tac[generates_subpartition_common_refinement_refines]
  \\ `restrict_partition (common_refinement w (b DIFF c)) z
      refines (restrict_partition ys z)`
  by (
    irule refines_transitive
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ irule imp_restrict_partition_refines
    \\ conj_tac >- metis_tac[common_refinement_partitions]
    \\ irule common_refinement_SUBSET
    \\ simp[]
    \\ metis_tac[factorises_def] )
  \\ `generates_subpartition w b (b DIFF c) (restrict_partition ys z)`
  by (
    qmatch_asmsub_abbrev_tac`d SUBSET bc`
    \\ simp[generates_subpartition_common_refinement_refines]
    \\ conj_tac >- simp[Abbr`bc`, SUBSET_DEF]
    \\ fs[Once EXTENSION, PULL_EXISTS, EXISTS_PROD] )
  \\ `{ chim w b c s t | (s,t) | s IN x INTER z /\ t IN z } = x INTER z`
  by (
    rewrite_tac[SET_EQ_SUBSET]
    \\ reverse conj_tac
    >- (
      simp[SUBSET_DEF]
      \\ qx_gen_tac`f` \\ strip_tac
      \\ qexistsl_tac[`f`,`f`]
      \\ DEP_REWRITE_TAC[chim_same]
      \\ metis_tac[SUBSET_DEF] )
    \\ Cases_on`x INTER z = {}`
    >- ( pop_assum SUBST_ALL_TAC \\ simp[] )
    \\ `x INTER z IN restrict_partition xs z`
    by (
      simp[restrict_partition_def]
      \\ `∃q. q IN x INTER z` by metis_tac[MEMBER_NOT_EMPTY]
      \\ qexists_tac`q`
      \\ fs[]
      \\ AP_THM_TAC
      \\ AP_TERM_TAC
      \\ irule part_unique
      \\ metis_tac[SUBSET_DEF] )
    \\ metis_tac[generates_subpartition_subsets] )
  \\ `mpoly_mul Reals (ffs_poly c (x INTER z)) (ffs_poly (b DIFF c) z) =
      ffs_poly (c UNION (b DIFF c))
        (IMAGE (λ(s,t). chim w b c s t) ((x INTER z) × z))`
  by (
    irule EQ_SYM
    \\ irule ffs_poly_union_chim_mul
    \\ simp[IN_DISJOINT]
    \\ metis_tac[INTER_SUBSET, SUBSET_TRANS] )
  \\ `mpoly_mul Reals (ffs_poly c z) (ffs_poly (b DIFF c) (y INTER z)) =
      ffs_poly (c UNION (b DIFF c))
        (IMAGE (λ(s,t). chim w b c s t) (z × (y INTER z)))`
  by (
    irule EQ_SYM
    \\ irule ffs_poly_union_chim_mul
    \\ simp[IN_DISJOINT]
    \\ metis_tac[INTER_SUBSET, SUBSET_TRANS] )
  \\ `c UNION (b DIFF c) = b` by (fs[EXTENSION, SUBSET_DEF] \\ metis_tac[])
  \\ pop_assum SUBST_ALL_TAC
  \\ `IMAGE (λ(s,t). chim w b c s t) ((x INTER z) × z) = x INTER z`
  by (
    qmatch_goalsub_abbrev_tac`lhs = _`
    \\ qpat_x_assum`_ = x INTER z`(SUBST1_TAC o SYM)
    \\ simp[Abbr`lhs`, Once EXTENSION, PULL_EXISTS, EXISTS_PROD] )
  \\ pop_assum SUBST_ALL_TAC
  \\ `{ chim w b c s t | (s,t) | s IN z /\ t IN y INTER z } = y INTER z`
  by (
    rewrite_tac[SET_EQ_SUBSET]
    \\ reverse conj_tac
    >- (
      simp[SUBSET_DEF]
      \\ qx_gen_tac`f` \\ strip_tac
      \\ qexistsl_tac[`f`,`f`]
      \\ DEP_REWRITE_TAC[chim_same]
      \\ metis_tac[SUBSET_DEF] )
    \\ Cases_on`y INTER z = {}`
    >- ( pop_assum SUBST_ALL_TAC \\ simp[] )
    \\ `y INTER z IN restrict_partition ys z`
    by (
      simp[restrict_partition_def]
      \\ `∃q. q IN y INTER z` by metis_tac[MEMBER_NOT_EMPTY]
      \\ qexists_tac`q`
      \\ fs[]
      \\ AP_THM_TAC
      \\ AP_TERM_TAC
      \\ irule part_unique
      \\ metis_tac[SUBSET_DEF] )
    \\ drule(#1(EQ_IMP_RULE generates_subpartition_subsets))
    \\ qmatch_goalsub_abbrev_tac`bc SUBSET _`
    \\ qmatch_goalsub_abbrev_tac`_ ⇒ _ SUBSET yz`
    \\ simp[]
    \\ strip_tac
    \\ first_x_assum drule
    \\ rw[SUBSET_DEF, PULL_EXISTS]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ qunabbrev_tac`bc`
    \\ DEP_REWRITE_TAC[chim_DIFF]
    \\ simp[]
    \\ metis_tac[partitions_thm, SUBSET_DEF, IN_INTER] )
  \\ `IMAGE (λ(s,t). chim w b c s t) (z × (y INTER z)) = y INTER z`
  by (
    qmatch_goalsub_abbrev_tac`lhs = _`
    \\ qpat_x_assum`_ = y INTER z`(SUBST1_TAC o SYM)
    \\ simp[Abbr`lhs`, Once EXTENSION, PULL_EXISTS, EXISTS_PROD] )
  \\ pop_assum SUBST_ALL_TAC
  \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
  \\ conj_tac
  >- (
    simp[]
    \\ metis_tac[INTER_FINITE, INTER_COMM, SUBSET_FINITE,
                 INTER_ASSOC, INTER_SUBSET, SUBSET_TRANS] )
  \\ qpat_x_assum`_ = ffs_poly _ _`(SUBST_ALL_TAC o SYM)
  \\ qpat_x_assum`_ = ffs_poly _ _`(SUBST_ALL_TAC o SYM)
  \\ `{chim w b c s t | s IN x INTER z /\ t IN y INTER z} SUBSET x INTER z`
  by (
    qmatch_goalsub_abbrev_tac`lhs SUBSET _`
    \\ qpat_x_assum`_ = x INTER z`(SUBST1_TAC o SYM)
    \\ simp[Abbr`lhs`, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `{chim w b c s t | s IN x INTER z /\ t IN y INTER z} SUBSET y INTER z`
  by (
    qmatch_goalsub_abbrev_tac`lhs SUBSET _`
    \\ qpat_x_assum`_ = y INTER z`(SUBST1_TAC o SYM)
    \\ simp[Abbr`lhs`, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ qmatch_asmsub_abbrev_tac`xzyz SUBSET _`
  \\ `xzyz = x INTER y INTER z`
  by (
    rewrite_tac[SET_EQ_SUBSET]
    \\ conj_tac >- fs[SUBSET_DEF]
    \\ irule SUBSET_TRANS
    \\ qexists_tac`{chim w b c s t | s IN x INTER y INTER z /\ t IN x INTER y INTER z }`
    \\ conj_tac
    >- (
      simp[SUBSET_DEF]
      \\ qx_gen_tac`f` \\ strip_tac
      \\ qexistsl_tac[`f`,`f`]
      \\ DEP_REWRITE_TAC[chim_same]
      \\ simp[] \\ metis_tac[SUBSET_DEF] )
    \\ simp[Abbr`xzyz`, SUBSET_DEF, PULL_EXISTS]
    \\ metis_tac[] )
  \\ `mpoly_mul Reals (ffs_poly c (x INTER z)) (ffs_poly (b DIFF c) (y INTER z))
      = ffs_poly (c UNION (b DIFF c))
          (IMAGE (λ(s,t). chim w b c s t) ((x INTER z) × (y INTER z)))`
  by (
    irule EQ_SYM
    \\ irule ffs_poly_union_chim_mul
    \\ simp[IN_DISJOINT]
    \\ metis_tac[INTER_SUBSET, SUBSET_TRANS] )
  \\ qmatch_asmsub_abbrev_tac`_ = ffs_poly _ zzz`
  \\ `zzz = xzyz`
  by (
    qunabbrev_tac`zzz`
    \\ qunabbrev_tac`xzyz`
    \\ simp[Once EXTENSION, PULL_EXISTS, EXISTS_PROD] )
  \\ qunabbrev_tac`zzz`
  \\ pop_assum SUBST_ALL_TAC
  \\ `c UNION (b DIFF c) = b` by (fs[EXTENSION, SUBSET_DEF] \\ metis_tac[])
  \\ pop_assum SUBST_ALL_TAC
  \\ qunabbrev_tac`xzyz`
  \\ qpat_x_assum`_ = _ INTER _`SUBST_ALL_TAC
  \\ pop_assum (SUBST_ALL_TAC o SYM)
  \\ `ffs_poly b z = ffs_poly (c UNION (b DIFF c))
         (IMAGE (λ(s,t). chim w b c s t) (z × z))`
  by (
    simp[]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ fs[EXTENSION, SUBSET_DEF]
    \\ metis_tac[] )
  \\ pop_assum SUBST1_TAC
  \\ DEP_REWRITE_TAC[ffs_poly_union_chim_mul]
  \\ conj_tac >- ( simp[IN_DISJOINT] \\ metis_tac[] )
  \\ qmatch_goalsub_abbrev_tac`f (f aa bb) (f cc dd) = _`
  \\ `mpoly Reals aa /\ mpoly Reals bb /\ mpoly Reals cc /\ mpoly Reals dd`
  by (
    unabbrev_all_tac
    \\ DEP_REWRITE_TAC[mpoly_ffs_poly]
    \\ metis_tac[FINITE_INTER, SUBSET_FINITE] )
  \\ qunabbrev_tac`f`
  \\ DEP_ONCE_REWRITE_TAC[mpoly_mul_comm]
  \\ conj_tac >- metis_tac[mpoly_def, RingReals, mpoly_mpoly_mul]
  \\ DEP_REWRITE_TAC[mpoly_mul_assoc]
  \\ conj_tac >- metis_tac[mpoly_def, RingReals, mpoly_mpoly_mul]
  \\ AP_TERM_TAC
  \\ DEP_ONCE_REWRITE_TAC[GSYM mpoly_mul_assoc]
  \\ conj_tac >- metis_tac[mpoly_def, RingReals, mpoly_mpoly_mul]
  \\ DEP_ONCE_REWRITE_TAC[mpoly_mul_comm]
  \\ conj_tac >- metis_tac[mpoly_def, RingReals, mpoly_mpoly_mul]
  \\ AP_TERM_TAC
  \\ DEP_ONCE_REWRITE_TAC[mpoly_mul_comm]
  \\ metis_tac[mpoly_def, RingReals, mpoly_mpoly_mul]
QED

Theorem ffs_poly_atom:
  FINITE w /\ b factorises w /\ e <> {} /\ e SUBSET w /\
  c IN ffs_irr w b e ==>
  irreducible (mpoly_ring Reals (POW w)) (ffs_poly c e)
Proof
  strip_tac
  \\ `FINITE e` by metis_tac[SUBSET_FINITE]
  \\ simp[ringIdealTheory.irreducible_def]
  \\ simp[ring_nonzero_eq, GSYM CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    simp[mpoly_ring_def]
    \\ irule support_ffs_poly_SUBSET_POW
    \\ fs[ffs_irr_def]
    \\ metis_tac[] )
  \\ conj_asm1_tac
  >- simp[mpoly_ring_def, Reals_def, ffs_poly_eq_zero]
  \\ conj_asm1_tac
  >- (
    simp[monoidOrderTheory.Invertibles_property]
    \\ simp[monoidOrderTheory.monoid_invertibles_element]
    \\ simp[mpoly_ring_def]
    \\ qx_gen_tac`q`
    \\ spose_not_then strip_assume_tac
    \\ qmatch_asmsub_abbrev_tac`mm p q = _`
    \\ `mm p (mm p q) = mm p (mpoly_one Reals)` by simp[]
    \\ `mpoly Reals p` by simp[Abbr`p`]
    \\ `mm p (mpoly_one Reals) = p` by metis_tac[mpoly_mul_one, RingReals]
    \\ `mpoly Reals (mm p q)` by metis_tac[mpoly_mpoly_mul, RingReals, mpoly_def]
    \\ `support Reals p SUBSET POW w` by fs[mpoly_ring_def, mpoly_def]
    \\ `support Reals (mm p q) SUBSET POW w`
    by (
      irule SUBSET_TRANS
      \\ qexists_tac`support Reals p UNION support Reals q`
      \\ simp[support_mpoly_mul_SUBSET] )
    \\ `support Reals p <> {} ==> support Reals (mm p q) = {}`
    by (
      rewrite_tac[GSYM DISJ_EQ_IMP]
      \\ irule ffs_poly_irreducible \\ metis_tac[] )
    \\ Cases_on`support Reals p = {}`
    >- (
      pop_assum mp_tac
      \\ simp[Abbr`p`, support_ffs_poly, IMAGE_EQ_SING]
      \\ fs[ffs_irr_def]
      \\ metis_tac[MEMBER_NOT_EMPTY] )
    \\ `support Reals (mm p q) = support Reals p UNION support Reals q`
    by (
      qunabbrev_tac`mm`
      \\ irule support_mpoly_mul
      \\ simp[]
      \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_POW]
      \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_POW]
      \\ fs[mpoly_ring_def]
      \\ strip_tac
      \\ `mpoly_mul Reals p q = K Reals.sum.id`
      by ( irule imp_mpoly_mul_zero \\ simp[] )
      \\ qpat_x_assum`mpoly_mul Reals p q = mpoly_one _`mp_tac
      \\ simp[mpoly_one_def, Once FUN_EQ_THM, Reals_def]
      \\ qexists_tac`{||}` \\ rw[] )
    \\ gs[] )
  \\ qx_genl_tac[`p`,`q`]
  \\ simp[monoidOrderTheory.Invertibles_property]
  \\ simp[monoidOrderTheory.monoid_invertibles_element]
  \\ simp[mpoly_ring_def]
  \\ strip_tac
  \\ ntac 5 (pop_assum mp_tac)
  \\ rewrite_tac[AND_IMP_INTRO]
  \\ qho_match_abbrev_tac`pQ p q ==> pP p ∨ pP q`
  \\ `∀p q. pQ p q /\ support Reals p = {} ==> pP p` suffices_by (
    rpt strip_tac
    \\ `pQ q p`
    by (
      fs[Abbr`pQ`]
      \\ irule mpoly_mul_comm
      \\ metis_tac[mpoly_def, RingReals] )
    \\ PROVE_TAC[ffs_poly_irreducible] )
  \\ simp[Abbr`pQ`, Abbr`pP`]
  \\ rpt strip_tac
  \\ fs[empty_support]
  \\ Cases_on`monomials Reals p = {}`
  >- (
    imp_res_tac imp_mpoly_mul_zero \\ fs[]
    \\ fs[ffs_poly_eq_zero, Reals_def] )
  \\ Cases_on`monomials Reals p` \\ fs[]
  \\ Cases_on`t` \\ gs[]
  \\ `Ring Reals` by simp[]
  \\ drule_then (drule_then drule) constant_mpoly_invertible
  \\ simp[]
  \\ impl_tac
  >- (
    strip_tac \\ fs[monomials_def, rrestrict_def]
    \\ fs[Reals_def, Once EXTENSION]
    \\ metis_tac[] )
  \\ rw[]
  \\ qmatch_asmsub_abbrev_tac`mpoly_mul Reals p ppi = _`
  \\ qexists_tac`ppi` \\ simp[]
  \\ conj_asm1_tac
  >- (
    rw[Abbr`ppi`]
    >- (
      irule mpoly_one_mono
      \\ simp[]
      \\ simp[Reals_def] )
    \\ simp[support_one_mono] )
  \\ metis_tac[mpoly_mul_comm, mpoly_def, RingReals]
QED

Theorem char_poly_factorises_imp_conditionally_orthogonal:
  FINITE w /\ b factorises w /\
  xs partitions w /\ ys partitions w /\ zs partitions w /\
  (∀x y z.
     x IN xs /\ y IN ys /\ z IN zs ==>
   ?q. mpoly Reals q /\ FINITE (support Reals q) /\
       mpoly_mul Reals (char_poly b z) q =
       mpoly_mul Reals (char_poly b (x INTER z)) (char_poly b (y INTER z)))
  ==> conditionally_orthogonal w b xs ys zs
Proof
  strip_tac
  \\ `FINITE b` by metis_tac[factorises_FINITE]
  \\ simp[conditionally_orthogonal_def]
  \\ qx_gen_tac`z` \\ strip_tac
  \\ simp[IN_DISJOINT]
  \\ qmatch_assum_rename_tac`bs factorises w`
  \\ qx_gen_tac`b`
  \\ spose_not_then strip_assume_tac
  \\ `z <> {} /\ z SUBSET w` by metis_tac[partitions_thm]
  \\ `is_subpartition w (restrict_partition xs z)`
  by simp[is_subpartition_restrict]
  \\ `is_subpartition w (restrict_partition ys z)`
  by simp[is_subpartition_restrict]
  \\ `b IN bs`
  by metis_tac[subpart_history_SUBSET_factorisation, SUBSET_DEF]
  \\ `ffs_irr w bs z partitions bs`
  by ( irule ffs_irr_partitions \\ simp[] )
  \\ `∃cs. cs IN ffs_irr w bs z /\ b IN cs`
  by (
    qexists_tac`part (ffs_irr w bs z) b`
    \\ conj_tac >- metis_tac[part_in_partition]
    \\ irule in_part \\ metis_tac[] )
  \\ first_assum(mp_then (Pat`ffs_irr`) mp_tac ffs_poly_atom)
  \\ strip_tac \\ rfs[]
  \\ qmatch_asmsub_abbrev_tac`irreducible _ p`
  \\ qmatch_asmsub_abbrev_tac`_ ∧ mm (char_poly bs _) _ = _`
  \\ `mpoly Reals p`
  by (
    simp[Abbr`p`]
    \\ irule mpoly_ffs_poly
    \\ imp_res_tac partitions_FINITE )
  \\ `∃pc. char_poly bs z = mm p pc ∧ mpoly Reals pc ∧
           support Reals pc SUBSET POW w`
  by (
    DEP_REWRITE_TAC[Q.SPEC`POW w`(Q.GEN`s`char_poly_ffs_poly_irr)]
    \\ `ffs_irr w bs z = cs INSERT (ffs_irr w bs z DELETE cs)`
    by simp[INSERT_DELETE]
    \\ pop_assum SUBST1_TAC
    \\ conj_tac >- simp[]
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ DEP_REWRITE_TAC[BAG_IMAGE_FINITE_INSERT]
    \\ imp_res_tac partitions_FINITE \\ simp[]
    \\ DEP_REWRITE_TAC[GBAG_INSERT]
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ qmatch_goalsub_abbrev_tac`rr.prod`
    \\ `rr.prod.op = mm` by simp[Abbr`rr`, mpoly_ring_def]
    \\ `Ring rr` by simp[Abbr`rr`]
    \\ `AbelianMonoid rr.prod` by metis_tac[Ring_def]
    \\ qmatch_goalsub_abbrev_tac`rr.prod.op p pc`
    \\ qexists_tac`pc` \\ simp[]
    \\ conj_asm1_tac
    >- (
      simp[Abbr`rr`, mpoly_ring_def, Abbr`p`]
      \\ simp[support_ffs_poly, SUBSET_DEF, PULL_EXISTS]
      \\ simp[IN_POW]
      \\ metis_tac[SUBSET_DEF, part_in_partition,
                   factorises_def, partitions_thm])
    \\ `pc IN rr.prod.carrier`
    by (
      qunabbrev_tac`pc`
      \\ irule GBAG_in_carrier
      \\ simp[SUBSET_DEF ,PULL_EXISTS] )
    \\ pop_assum mp_tac
    \\ simp[Abbr`rr`, mpoly_ring_def]
    \\ simp[SUBSET_DEF])
  \\ `¬(∀x. x IN xs ==> ?q. mm p q = char_poly bs (x INTER z) ∧
                            mpoly Reals q ∧ support Reals q SUBSET POW w) ⇒
      (∀y. y IN ys ==> ?q. mm p q = char_poly bs (y INTER z) ∧
                            mpoly Reals q ∧ support Reals q SUBSET POW w)`
  by (
    spose_not_then strip_assume_tac
    \\ first_x_assum(qspecl_then[`x`,`y`,`z`]mp_tac)
    \\ impl_tac >- simp[]
    \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`_ = mm p1 p2`
    \\ `mm p (mm pc q) = mm p1 p2`
    by (
      qunabbrev_tac`mm`
      \\ DEP_REWRITE_TAC[GSYM mpoly_mul_assoc]
      \\ simp[] \\ rfs[]
      \\ fs[mpoly_def] )
    \\ `support Reals (mm p1 p2) SUBSET POW w`
    by (
      irule SUBSET_TRANS
      \\ qexists_tac`support Reals p1 UNION support Reals p2`
      \\ qunabbrev_tac`mm`
      \\ DEP_REWRITE_TAC[support_mpoly_mul_SUBSET]
      \\ qunabbrev_tac`p1` \\ qunabbrev_tac`p2`
      \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
      \\ simp[]
      \\ DEP_REWRITE_TAC[Q.GEN`b`support_ffs_poly_SUBSET_POW]
      \\ metis_tac[INTER_FINITE, INTER_COMM, SUBSET_FINITE, SUBSET_REFL,
                   INTER_ASSOC, INTER_SUBSET, SUBSET_TRANS] )
    \\ `support Reals q SUBSET POW w`
    by (
      `support Reals (char_poly bs z) ∪ support Reals q =
       support Reals (mm p1 p2)`
      by (
        qpat_x_assum`mm _ q = mm _ _`(SUBST1_TAC o SYM)
        \\ irule EQ_SYM
        \\ qunabbrev_tac`mm`
        \\ irule support_mpoly_mul
        \\ `FINITE z` by metis_tac[partitions_FINITE]
        \\ simp[]
        \\ conj_tac
        >- (
          simp[Once Reals_def, SimpRHS]
          \\ strip_tac
          \\ fs[char_poly_eq_zero] )
        \\ strip_tac
        \\ `mpoly_mul Reals pc q = K Reals.sum.id`
        by ( irule imp_mpoly_mul_zero \\ simp[] )
        \\ fs[]
        \\ `mpoly_mul Reals p (K Reals.sum.id) = K Reals.sum.id`
        by ( irule imp_mpoly_mul_zero \\ simp[] )
        \\ fs[]
        \\ `IntegralDomain (mpoly_ring Reals (POW w))` by (
          irule mpoly_integral_domain \\ simp[] )
        \\ fs[IntegralDomain_def]
        \\ first_x_assum(qspecl_then[`p1`,`p2`]mp_tac)
        \\ simp[mpoly_ring_def]
        \\ simp[GSYM CONJ_ASSOC]
        \\ conj_tac >- metis_tac[mpoly_char_poly, INTER_FINITE, INTER_COMM]
        \\ conj_tac >- (
          qunabbrev_tac`p1`
          \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
          \\ DEP_REWRITE_TAC[Q.GEN`b`support_ffs_poly_SUBSET_POW]
          \\ simp[]
          \\ metis_tac[INTER_FINITE, SUBSET_DEF, IN_INTER, INTER_COMM] )
        \\ conj_tac >- metis_tac[mpoly_char_poly, INTER_FINITE, INTER_COMM]
        \\ conj_tac >- (
          qunabbrev_tac`p2`
          \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
          \\ DEP_REWRITE_TAC[Q.GEN`b`support_ffs_poly_SUBSET_POW]
          \\ simp[]
          \\ metis_tac[INTER_FINITE, SUBSET_DEF, IN_INTER, INTER_COMM] )
        \\ simp[Abbr`p1`, Abbr`p2`, Reals_def]
        \\ conj_tac \\ strip_tac
        \\ first_x_assum(qspec_then`K Reals.sum.id`mp_tac)
        \\ first_x_assum(qspec_then`K Reals.sum.id`mp_tac)
        \\ DEP_REWRITE_TAC[imp_mpoly_mul_zero]
        \\ simp[Reals_def] )
      \\ ntac 2 (pop_assum mp_tac)
      \\ simp[Once EXTENSION]
      \\ simp[SUBSET_DEF]
      \\ metis_tac[] )
    \\ `cs SUBSET bs` by fs[SUBSET_DEF, ffs_irr_def]
    \\ `ring_divides (mpoly_ring Reals (POW w)) p (mm p1 p2)`
    by (
      simp[ringDividesTheory.ring_divides_def]
      \\ qexists_tac`mm pc q`
      \\ qmatch_goalsub_abbrev_tac`rr.carrier`
      \\ `mm = rr.prod.op` by simp[Abbr`rr`,mpoly_ring_def]
      \\ `pc IN rr.carrier /\ q IN rr.carrier` by (
        simp[Abbr`rr`]
        \\ simp_tac(srw_ss()++boolSimps.LET_ss)[mpoly_ring_def]
        \\ metis_tac[] )
      \\ `Ring rr` by simp[Abbr`rr`]
      \\ conj_asm1_tac >- metis_tac[ring_mult_element]
      \\ `p IN rr.carrier`
      by (
        simp[Abbr`rr`, Abbr`p`]
        \\ simp_tac(srw_ss()++boolSimps.LET_ss)[mpoly_ring_def]
        \\ simp[]
        \\ irule (Q.GEN`b`support_ffs_poly_SUBSET_POW)
        \\ metis_tac[] )
      \\ metis_tac[ring_mult_comm] )
    \\ qmatch_asmsub_abbrev_tac`ring_divides rr`
    \\ `¬ring_divides rr p p1`
    by (
      simp[ringDividesTheory.ring_divides_def]
      \\ `p IN rr.carrier` by (
        simp[Abbr`rr`, mpoly_ring_def, Abbr`p`]
        \\ irule support_ffs_poly_SUBSET_POW
        \\ metis_tac[] )
      \\ `mm = rr.prod.op` by simp[Abbr`rr`, mpoly_ring_def]
      \\ `Ring rr` by simp[Abbr`rr`]
      \\ rpt strip_tac
      \\ `p1 = rr.prod.op p s` by metis_tac[ring_mult_comm]
      \\ qpat_x_assum`s IN _`mp_tac
      \\ simp_tac(srw_ss()++boolSimps.LET_ss)[Abbr`rr`, mpoly_ring_def]
      \\ metis_tac[] )
    \\ `¬ring_divides rr p p2`
    by (
      simp[ringDividesTheory.ring_divides_def]
      \\ `p IN rr.carrier` by (
        simp[Abbr`rr`, mpoly_ring_def, Abbr`p`]
        \\ irule support_ffs_poly_SUBSET_POW
        \\ metis_tac[] )
      \\ `mm = rr.prod.op` by simp[Abbr`rr`, mpoly_ring_def]
      \\ `Ring rr` by simp[Abbr`rr`]
      \\ rpt strip_tac
      \\ `p2 = rr.prod.op p s` by metis_tac[ring_mult_comm]
      \\ qpat_x_assum`s IN _`mp_tac
      \\ simp_tac(srw_ss()++boolSimps.LET_ss)[Abbr`rr`, mpoly_ring_def]
      \\ metis_tac[] )
    \\ `ring_prime rr p`
    by (
      irule UniqueFactorizationDomain_irreducible_prime
      \\ simp[]
      \\ qunabbrev_tac`rr`
      \\ irule UniqueFactorizationDomain_mpoly
      \\ simp[] )
    \\ `mm = rr.prod.op` by simp[Abbr`rr`, mpoly_ring_def]
    \\ `p1 IN rr.carrier /\ p2 IN rr.carrier`
    by (
      simp[Abbr`rr`]
      \\ simp_tac(srw_ss()++boolSimps.LET_ss)[mpoly_ring_def]
      \\ simp_tac std_ss [Abbr`p1`, Abbr`p2`]
      \\ DEP_REWRITE_TAC[support_char_poly_SUBSET_POW]
      \\ DEP_REWRITE_TAC[mpoly_char_poly]
      \\ simp[]
      \\ metis_tac[INTER_FINITE, INTER_COMM, SUBSET_FINITE, SUBSET_REFL,
                   INTER_ASSOC, INTER_SUBSET, SUBSET_TRANS] )
    \\ metis_tac[ringDividesTheory.ring_prime_def] )
  \\ pop_assum mp_tac
  \\ simp[]
  \\ qho_match_abbrev_tac`P xs /\ P ys`
  \\ rpt(qhdtm_x_assum`is_subpartition`mp_tac)
  \\ rpt(qpat_x_assum`b IN subpart_history _ _ _`mp_tac)
  \\ qpat_x_assum`!x. _`mp_tac
  \\ qpat_x_assum`xs partitions _`mp_tac
  \\ qpat_x_assum`ys partitions _`mp_tac
  \\ simp[AND_IMP_INTRO]
  \\ qho_match_abbrev_tac`Q xs ys ==> P xs /\ P ys`
  \\ `∀xs ys. Q xs ys <=> Q ys xs`
  by (
    rw[Abbr`Q`]
    \\ rw[EQ_IMP_THM]
    \\ first_x_assum drule
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ qmatch_assum_rename_tac`u IN zs`
    \\ `FINITE u` by metis_tac[partitions_FINITE]
    \\ qexists_tac`q` \\ simp[]
    \\ qunabbrev_tac`mm`
    \\ irule mpoly_mul_comm
    \\ simp[]
    \\ metis_tac[IMAGE_FINITE, INTER_FINITE, INTER_COMM] )
  \\ `∀xs ys. Q xs ys ==> P xs` suffices_by metis_tac[]
  \\ pop_assum kall_tac
  \\ rw[Abbr`Q`, Abbr`P`]
  \\ spose_not_then strip_assume_tac
  \\ `w <> {}` by (strip_tac \\ fs[])
  \\ `xs <> {}` by metis_tac[empty_partitions]
  \\ `cs SUBSET bs` by fs[ffs_irr_def, SUBSET_DEF]
  \\ `support Reals p SUBSET POW w`
  by (
    qunabbrev_tac`p`
    \\ irule support_ffs_poly_SUBSET_POW
    \\ metis_tac[] )
  \\ `FINITE z` by metis_tac[SUBSET_FINITE, factorises_FINITE]
  \\ `!x. x IN xs ==> char_poly bs (x INTER z) =
      mm (ffs_poly cs z) (ffs_poly (bs DIFF cs) (x INTER z))`
  by (
    rpt strip_tac
    \\ Cases_on`x INTER z = {}`
    >- (
      simp[]
      \\ `char_poly bs {} = K 0` by metis_tac[char_poly_eq_zero, FINITE_EMPTY]
      \\ `ffs_poly (bs DIFF cs) {} = K 0` by metis_tac[ffs_poly_eq_zero, FINITE_EMPTY]
      \\ `mm p (K 0) = K Reals.sum.id`
      by (
        qunabbrev_tac`mm`
        \\ irule imp_mpoly_mul_zero
        \\ simp[empty_monomials]
        \\ simp[Reals_def] )
      \\ simp[Reals_def] )
    \\ first_assum drule \\ strip_tac
    \\ drule_then drule divides_char_poly_multiple_ffs_poly
    \\ `x INTER z SUBSET w` by fs[SUBSET_DEF]
    \\ disch_then drule
    \\ qunabbrev_tac`mm`
    \\ disch_then(first_assum o (mp_then (Pat`mpoly_mul`) mp_tac))
    \\ impl_tac >- metis_tac[FINITE_POW, SUBSET_FINITE]
    \\ disch_then(qx_choosel_then[`rp`,`cp`]strip_assume_tac)
    \\ drule_then drule divides_char_poly_multiple_ffs_poly
    \\ disch_then drule
    \\ `mpoly_mul Reals q p = char_poly bs (x INTER z)`
    by (
      qpat_x_assum`_ = char_poly _ _`(SUBST1_TAC o SYM)
      \\ irule mpoly_mul_comm
      \\ metis_tac[mpoly_def, RingReals] )
    \\ disch_then(first_assum o (mp_then (Pat`mpoly_mul`) mp_tac))
    \\ impl_tac >- metis_tac[FINITE_POW, SUBSET_FINITE]
    \\ disch_then(qx_choosel_then[`rq`,`cq`]strip_assume_tac)
    \\ Cases_on`rp = 0`
    >- (
      `rp = Reals.sum.id` by simp[Reals_def]
      \\ `p = K Reals.sum.id`
      by (
        qpat_x_assum`p = _`SUBST_ALL_TAC
        \\ pop_assum SUBST1_TAC
        \\ `$* = Reals.prod.op` by simp[Reals_def]
        \\ pop_assum SUBST1_TAC
        \\ irule cmul_zero
        \\ simp[]
        \\ irule mpoly_ffs_poly
        \\ metis_tac[INTER_FINITE, INTER_COMM])
      \\ `mpoly_mul Reals p q = K Reals.sum.id`
      by ( irule imp_mpoly_mul_zero \\ simp[] )
      \\ `char_poly bs (x INTER z) = K 0` by fs[]
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC[char_poly_eq_zero]
      \\ simp[]
      \\ metis_tac[INTER_COMM, FINITE_INTER] )
    \\ Cases_on`rq = 0`
    >- (
      `rq = Reals.sum.id` by simp[Reals_def]
      \\ `q = K Reals.sum.id`
      by (
        qpat_x_assum`q = _`SUBST_ALL_TAC
        \\ pop_assum SUBST1_TAC
        \\ `$* = Reals.prod.op` by simp[Reals_def]
        \\ pop_assum SUBST1_TAC
        \\ irule cmul_zero
        \\ simp[]
        \\ irule mpoly_ffs_poly
        \\ metis_tac[INTER_FINITE, INTER_COMM])
      \\ `mpoly_mul Reals p q = K Reals.sum.id`
      by ( irule imp_mpoly_mul_zero \\ simp[] )
      \\ `char_poly bs (x INTER z) = K 0` by fs[]
      \\ pop_assum mp_tac
      \\ DEP_REWRITE_TAC[char_poly_eq_zero]
      \\ simp[]
      \\ metis_tac[INTER_COMM, FINITE_INTER] )
    \\ `mpoly Reals (ffs_poly cp (x INTER z)) ∧
        mpoly Reals (ffs_poly cq (x INTER z))`
    by (
      DEP_REWRITE_TAC[mpoly_ffs_poly]
      \\ metis_tac[INTER_FINITE, INTER_COMM] )
    \\ `cp = cs`
    by (
      `∃s. s IN x INTER z` by metis_tac[MEMBER_NOT_EMPTY]
      \\ simp[Once EXTENSION]
      \\ qx_gen_tac`y`
      \\ reverse(Cases_on`y IN bs`) >- metis_tac[SUBSET_DEF]
      \\ `y IN cs ⇔ part y s ∈ support Reals p`
      by (
        simp_tac(srw_ss())[Abbr`p`, support_ffs_poly, PULL_EXISTS]
        \\ eq_tac \\ strip_tac
        >- metis_tac[IN_INTER]
        \\ qmatch_assum_rename_tac`f IN cs`
        \\ Cases_on`y = f` \\ simp[]
        \\ `part y s IN y`
        by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
        \\ `part y s IN f`
        by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
        \\ `DISJOINT y f` by metis_tac[factors_DISJOINT, SUBSET_DEF]
        \\ metis_tac[IN_DISJOINT] )
      \\ `y IN cp ⇔ part y s ∈ support Reals p`
      by (
        simp[]
        \\ DEP_REWRITE_TAC[support_cmul_Reals]
        \\ simp[GSYM CONJ_ASSOC]
        \\ simp_tac(srw_ss())[support_ffs_poly, PULL_EXISTS]
        \\ eq_tac \\ strip_tac
        >- metis_tac[IN_INTER]
        \\ qmatch_assum_rename_tac`f IN cp`
        \\ Cases_on`y = f` \\ simp[]
        \\ `part y s IN y`
        by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
        \\ `part y s IN f`
        by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
        \\ `DISJOINT y f` by metis_tac[factors_DISJOINT, SUBSET_DEF]
        \\ metis_tac[IN_DISJOINT] )
      \\ simp[] )
    \\ `DISJOINT (support Reals p) (support Reals q)`
    by (
      simp_tac std_ss [IN_DISJOINT]
      \\ spose_not_then strip_assume_tac
      \\ qmatch_assum_rename_tac`v IN support Reals p`
      \\ `degree_of Reals (char_poly bs (x INTER z)) v >= 2`
      by (
        qpat_x_assum`mpoly_mul _ p _ = char_poly _ _`(SUBST1_TAC o SYM)
        \\ DEP_REWRITE_TAC[Q.GEN`s`degree_of_mpoly_mul]
        \\ conj_tac
        >- (
          qexists_tac`support Reals p ∪ support Reals q`
          \\ gs[]
          \\ conj_tac >- metis_tac[FINITE_POW, SUBSET_FINITE]
          \\ CCONTR_TAC
          \\ `char_poly bs (x INTER z) = K Reals.sum.id`
          by (
            qpat_x_assum`_ = char_poly _ _`(SUBST1_TAC o SYM)
            \\ irule imp_mpoly_mul_zero
            \\ pop_assum mp_tac \\ simp[]
            \\ strip_tac \\ simp[] )
          \\ pop_assum mp_tac
          \\ simp_tac(srw_ss())[Reals_def]
          \\ metis_tac[char_poly_eq_zero, INTER_FINITE, INTER_COMM])
        \\ imp_res_tac mpoly_def
        \\ imp_res_tac support_degree_of
        \\ DECIDE_TAC )
      \\ qmatch_asmsub_abbrev_tac`dd >= 2`
      \\ `dd <= 1` suffices_by DECIDE_TAC
      \\ qunabbrev_tac`dd`
      \\ irule degree_of_char_poly
      \\ simp[]
      \\ conj_tac >- metis_tac[INTER_COMM, INTER_FINITE]
      \\ qexists_tac`w`
      \\ fs[SUBSET_DEF] )
    \\ `cq = bs DIFF cs`
    by (
      `∃s. s IN x INTER z` by metis_tac[MEMBER_NOT_EMPTY]
      \\ simp[Once EXTENSION]
      \\ qx_gen_tac`y`
      \\ reverse(Cases_on`y IN bs`) >- metis_tac[SUBSET_DEF]
      \\ simp[]
      \\ reverse eq_tac \\ strip_tac
      >- (
        `part y s ∈ support Reals (char_poly bs (x INTER z))`
        by (
          simp_tac(srw_ss())[support_char_poly, PULL_EXISTS, EXISTS_PROD]
          \\ metis_tac[IN_INTER] )
        \\ `part y s IN support Reals q UNION support Reals p`
        by metis_tac[support_mpoly_mul_SUBSET, RingReals, SUBSET_DEF]
        \\ `part y s NOTIN support Reals p`
        by (
          qunabbrev_tac`p`
          \\ simp_tac(srw_ss())[support_ffs_poly, PULL_EXISTS, EXISTS_PROD]
          \\ rpt strip_tac
          \\ spose_not_then strip_assume_tac
          \\ qmatch_assum_rename_tac`f IN cs`
          \\ Cases_on`y = f` >- fs[]
          \\ `part y s IN y`
          by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
          \\ `part y s IN f`
          by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
          \\ `DISJOINT y f` by metis_tac[factors_DISJOINT, SUBSET_DEF]
          \\ metis_tac[IN_DISJOINT] )
        \\ `part y s IN support Reals q` by fs[]
        \\ pop_assum mp_tac
        \\ simp[]
        \\ DEP_REWRITE_TAC[support_cmul_Reals]
        \\ simp[GSYM CONJ_ASSOC]
        \\ simp[support_ffs_poly, PULL_EXISTS]
        \\ rpt strip_tac
        \\ spose_not_then strip_assume_tac
        \\ qmatch_assum_rename_tac`f IN cq`
        \\ Cases_on`y = f` >- fs[]
        \\ `part y s IN y`
        by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
        \\ `part y s IN f`
        by metis_tac[part_in_partition, factorises_def, SUBSET_DEF]
        \\ `DISJOINT y f` by metis_tac[factors_DISJOINT, SUBSET_DEF]
        \\ metis_tac[IN_DISJOINT] )
      \\ `part y s IN support Reals q`
      by (
        simp[]
        \\ DEP_REWRITE_TAC[support_cmul_Reals]
        \\ simp[GSYM CONJ_ASSOC]
        \\ simp[support_ffs_poly, PULL_EXISTS]
        \\ metis_tac[IN_INTER] )
      \\ `part y s NOTIN support Reals p` by metis_tac[IN_DISJOINT]
      \\ pop_assum mp_tac
      \\ simp[]
      \\ DEP_REWRITE_TAC[support_cmul_Reals]
      \\ fs[]
      \\ DEP_REWRITE_TAC[support_ffs_poly]
      \\ simp[PULL_EXISTS]
      \\ metis_tac[IN_INTER] )
    \\ `rp = 1`
    by (
      qpat_x_assum`p = _`mp_tac
      \\ simp[Once FUN_EQ_THM]
      \\ simp[Abbr`p`]
      \\ simp[ffs_poly_def]
      \\ rw[mono_bag_poly_def, BAG_OF_SET]
      \\ `∃s. s IN x INTER z` by metis_tac[MEMBER_NOT_EMPTY, IN_INTER]
      \\ first_x_assum(qspec_then`mono_bag cp s`mp_tac)
      \\ reverse IF_CASES_TAC >- metis_tac[IN_INTER]
      \\ reverse IF_CASES_TAC >- metis_tac[IN_INTER]
      \\ simp[] )
    \\ `rq = 1`
    by (
      first_assum (mp_then Any mp_tac DISJOINT_support_mpoly_mul)
      \\ impl_tac >- simp[]
      \\ Cases_on`monomials Reals p = {}`
      >- (
        `char_poly bs (x INTER z) = K Reals.sum.id`
        by metis_tac[imp_mpoly_mul_zero]
        \\ pop_assum mp_tac
        \\ `FINITE (x INTER z)` by metis_tac[INTER_FINITE, INTER_COMM]
        \\ simp[char_poly_eq_zero, Reals_def] )
      \\ Cases_on`monomials Reals q = {}`
      >- (
        `char_poly bs (x INTER z) = K Reals.sum.id`
        by metis_tac[imp_mpoly_mul_zero]
        \\ pop_assum mp_tac
        \\ `FINITE (x INTER z)` by metis_tac[INTER_FINITE, INTER_COMM]
        \\ simp[char_poly_eq_zero, Reals_def] )
      \\ `∃m1 m2. m1 IN monomials Reals p /\ m2 IN monomials Reals q`
      by metis_tac[MEMBER_NOT_EMPTY]
      \\ strip_tac
      \\ first_x_assum (drule_then drule)
      \\ `p m1 = 1`
      by (
        simp[ffs_poly_def, mono_bag_poly_def]
        \\ qpat_x_assum`m1 IN _`mp_tac
        \\ simp[BAG_OF_SET]
        \\ `$* = Reals.prod.op` by simp[Reals_def]
        \\ pop_assum SUBST1_TAC
        \\ DEP_REWRITE_TAC[monomials_cmul]
        \\ simp[]
        \\ fs[]
        \\ simp[Reals_def] )
      \\ `BAG_UNION m1 m2 ∈ monomials Reals (char_poly bs (x INTER z))`
      by ( rfs[] \\ simp[EXISTS_PROD] \\ metis_tac[] )
      \\ qpat_x_assum`mpoly_mul Reals p q = _`(SUBST1_TAC)
      \\ pop_assum mp_tac
      \\ simp[char_poly_def]
      \\ simp[mono_bag_poly_def, BAG_IMAGE_DEF, BAG_FILTER_BAG_OF_SET]
      \\ `FINITE (x INTER z)` by metis_tac[INTER_FINITE, INTER_COMM]
      \\ simp[]
      \\ simp[Reals_def]
      \\ simp[ffs_poly_def, mono_bag_poly_def, BAG_CARD_BAG_OF_SET]
      \\ simp[BAG_OF_SET]
      \\ reverse(rw[])
      >- (
        pop_assum mp_tac
        \\ simp[Once EXTENSION]
        \\ metis_tac[] )
      \\ qpat_x_assum`_ = mono_bag _ _`(SUBST1_TAC )
      \\ qmatch_goalsub_abbrev_tac`CARD s`
      \\ `SING s` suffices_by metis_tac[CARD_SING, SING_DEF]
      \\ simp[SING_DEF, Abbr`s`]
      \\ simp[Once EXTENSION]
      \\ metis_tac[mono_bag_inj, SUBSET_DEF] )
    \\ `$* rp = Reals.prod.op Reals.prod.id` by simp[Reals_def]
    \\ `$* rq = Reals.prod.op Reals.prod.id` by simp[Reals_def]
    \\ gs[cmul_one] )
  \\ `∀x. x IN xs ==> x INTER z =
            { chim w bs (bs DIFF cs) s t | s IN x INTER z ∧ t IN z }`
  by (
    rpt strip_tac
    \\ first_x_assum drule
    \\ qunabbrev_tac`mm`
    \\ DEP_REWRITE_TAC[GSYM (Q.SPEC`bs`(Q.GEN`b`ffs_poly_union_chim_mul))]
    \\ conj_asm1_tac >- ( simp[] \\ fs[SUBSET_DEF, IN_DISJOINT] \\ metis_tac[] )
    \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
    \\ conj_asm1_tac >- (simp[] \\ metis_tac[INTER_COMM, INTER_FINITE])
    \\ disch_then(mp_tac o Q.AP_TERM`monomials Reals`)
    \\ qmatch_goalsub_abbrev_tac`cs UNION bdc`
    \\ simp[monomials_ffs_poly]
    \\ `cs UNION bdc = bs` by (
      simp[Abbr`bdc`, Once EXTENSION]
      \\ metis_tac[SUBSET_DEF] )
    \\ pop_assum SUBST1_TAC
    \\ DEP_REWRITE_TAC[helperSetTheory.INJ_IMAGE_EQ]
    \\ conj_tac
    >- (
      qexists_tac`w`
      \\ simp[INJ_DEF]
      \\ conj_tac >- metis_tac[mono_bag_inj]
      \\ simp[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
      \\ metis_tac[chim_thm, SUBSET_DEF] )
    \\ disch_then SUBST1_TAC
    \\ simp[Once EXTENSION, PULL_EXISTS, EXISTS_PROD]
    \\ `x ⊆ w` by metis_tac[partitions_thm]
    \\ rw[EQ_IMP_THM]
    \\ TRY(qmatch_goalsub_rename_tac`chim w bs cs s t`)
    \\ qexistsl_tac[`t`,`s`]
    \\ qunabbrev_tac`bdc`
    \\ DEP_REWRITE_TAC[chim_DIFF]
    \\ metis_tac[SUBSET_DEF] )
  \\ `generates_subpartition w bs (bs DIFF cs) (restrict_partition xs z)`
  suffices_by (
    strip_tac
    \\ `subpart_history w bs (restrict_partition xs z) ⊆ bs DIFF cs`
    by metis_tac[subpart_history_thm]
    \\ `b IN bs /\ b NOTIN cs` by metis_tac[SUBSET_DEF, IN_DIFF] )
  \\ qmatch_goalsub_abbrev_tac`generates_subpartition _ _ bdc`
  \\ simp[generates_subpartition_subsets]
  \\ DEP_REWRITE_TAC[subpart_domain_restrict]
  \\ simp[]
  \\ conj_tac >- simp[Abbr`bdc`]
  \\ simp[restrict_partition_def]
  \\ rpt strip_tac
  \\ `part xs x IN xs` by metis_tac[part_in_partition, SUBSET_DEF]
  \\ first_x_assum drule
  \\ metis_tac[SET_EQ_SUBSET]
QED

Definition ffs_prob_space_def:
  ffs_prob_space w b p <=>
    prob_space p /\ p_space p = w /\ FINITE w /\ events p = POW w /\
    !x. x IN w ==>
    (prob p {x} =
       Normal (GBAG Reals.prod
                 (BAG_IMAGE (real o prob p o flip part x)
                   (BAG_OF_SET b))))
End

Theorem ffs_prob_space_char_poly:
  FINITE w /\ b factorises w /\
  prob_space p /\ p_space p = w /\ events p = POW w ==>
  (ffs_prob_space w b p <=>
   !e. e SUBSET w ==>
     real (prob p e) = mpoly_eval Reals (char_poly b e) (real o prob p))
Proof
  strip_tac
  \\ reverse eq_tac
  >- (
    simp[ffs_prob_space_def] \\ rw[]
    \\ first_x_assum(qspec_then`{x}`mp_tac)
    \\ simp[SUBSET_DEF]
    \\ imp_res_tac prob_normal
    \\ first_x_assum(qspec_then`{x}`mp_tac)
    \\ simp[SUBSET_DEF, IN_POW]
    \\ strip_tac \\ simp[]
    \\ strip_tac
    \\ imp_res_tac factorises_FINITE
    \\ simp[]
    \\ simp[char_poly_def, BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ simp[mpoly_eval_def, mono_bag_poly_sing]
    \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
    \\ qmatch_goalsub_abbrev_tac`GBAG g _`
    \\ simp[Reals_def, rrestrict_def]
    \\ simp[Abbr`g`]
    \\ simp[Once Reals_def]
    \\ simp[mono_bag_def]
    \\ simp[GSYM BAG_IMAGE_COMPOSE] )
  >- (
    simp[ffs_prob_space_def]
    \\ rpt strip_tac
    \\ `FINITE e` by metis_tac[SUBSET_FINITE]
    \\ DEP_ONCE_REWRITE_TAC[PROB_EXTREAL_SUM_IMAGE]
    \\ simp[IN_POW]
    \\ conj_asm1_tac >- metis_tac[SUBSET_DEF]
    \\ qpat_x_assum`!x. _ => _ = _`mp_tac
    \\ qho_match_abbrev_tac`(∀x. x IN w ==> f x = g x) ==> _`
    \\ strip_tac
    \\ `EXTREAL_SUM_IMAGE f e = EXTREAL_SUM_IMAGE g e`
    by (
      irule EXTREAL_SUM_IMAGE_EQ
      \\ simp[] \\ simp[Abbr`g`] )
    \\ simp[]
    \\ qunabbrev_tac`g`
    \\ pop_assum kall_tac
    \\ DEP_REWRITE_TAC[EXTREAL_SUM_IMAGE_NORMAL]
    \\ simp[]
    \\ simp[mpoly_eval_def]
    \\ simp[GBAG_Reals_sum_BAG_IMAGE_BAG_OF_SET]
    \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
    \\ imp_res_tac factorises_FINITE
    \\ simp[ffs_poly_def, mono_bag_poly_def]
    \\ simp[BAG_OF_SET]
    \\ simp[rrestrict_def]
    \\ qmatch_goalsub_abbrev_tac`GBAG g _`
    \\ simp[Reals_def]
    \\ DEP_REWRITE_TAC[real_sigmaTheory.REAL_SUM_IMAGE_IMAGE]
    \\ simp[]
    \\ conj_tac >- ( simp[INJ_DEF] \\ metis_tac[mono_bag_inj] )
    \\ simp[combinTheory.o_DEF]
    \\ irule real_sigmaTheory.REAL_SUM_IMAGE_EQ
    \\ simp[]
    \\ simp[Abbr`g`]
    \\ gen_tac \\ strip_tac
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ irule EQ_SYM
    \\ simp[Once Reals_def]
    \\ simp[mono_bag_def, GSYM BAG_IMAGE_COMPOSE]
    \\ simp[GSYM BAG_OF_SET]
    \\ simp[combinTheory.o_DEF])
QED

Theorem finite_mpoly_char_poly[simp]:
  FINITE b /\ FINITE z ==>
  finite_mpoly Reals (char_poly b z)
Proof
  rw[finite_mpoly_def, PULL_EXISTS]
  \\ rw[mono_bag_def]
QED

Theorem ffs_poly_decompose:
  !c. FINITE c ==>
  b factorises w /\ FINITE w /\ w <> {} /\ c SUBSET b ==>
  ffs_poly c w = GBAG (mpoly_ring Reals (POW w)).prod
                   (BAG_IMAGE (λv. ffs_poly {v} w) (BAG_OF_SET c))
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ rw[]
  >- (
    rw[ffs_poly_def, mono_bag_poly_def, Once FUN_EQ_THM]
    \\ rw[BAG_OF_SET, mpoly_ring_def, mpoly_one_def]
    \\ rw[Reals_def]
    \\ metis_tac[MEMBER_NOT_EMPTY] )
  \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT] \\ fs[]
  \\ DEP_REWRITE_TAC[GBAG_INSERT]
  \\ simp[]
  \\ `Ring (mpoly_ring Reals (POW w))` by simp[]
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_tac >- metis_tac[Ring_def]
  \\ qmatch_goalsub_abbrev_tac`_ = _ p1 p2`
  \\ simp[mpoly_ring_def]
  \\ simp[Once SUBSET_DEF, PULL_EXISTS]
  \\ simp[Abbr`p1`]
  \\ conj_tac
  >- (
    rw[]
    \\ irule support_ffs_poly_SUBSET_POW
    \\ simp[SUBSET_DEF]
    \\ fs[SUBSET_DEF]
    \\ metis_tac[] )
  \\ conj_tac
  >- (
    irule support_ffs_poly_SUBSET_POW
    \\ fs[SUBSET_DEF]
    \\ metis_tac[] )
  \\ qpat_x_assum`_ = p2`(SUBST1_TAC o SYM)
  \\ DEP_REWRITE_TAC[GSYM ffs_poly_union_chim_mul]
  \\ conj_tac >- simp[]
  \\ rewrite_tac[GSYM INSERT_SING_UNION]
  \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac`chim w b ee _ _`
  \\ simp[Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
  \\ `ee ⊆ b` by simp[SUBSET_DEF, Abbr`ee`]
  \\ conj_tac >- (
    rpt strip_tac
    \\ qexistsl_tac[`x`,`x`]
    \\ metis_tac[chim_same, SUBSET_DEF] )
  \\ metis_tac[chim_thm]
QED

Theorem mono_bag_poly_BAG_UNION:
  mono_bag_poly (BAG_UNION b1 b2) =
  mpoly_add Reals (mono_bag_poly b1) (mono_bag_poly b2)
Proof
  rw[mono_bag_poly_def, FUN_EQ_THM, mpoly_add_def]
  \\ rw[Reals_def, rrestrict_def]
  \\ rw[BAG_UNION]
QED

Theorem ffs_fundamental:
  FINITE w /\ b factorises w /\
  xs partitions w /\ ys partitions w /\ zs partitions w
  ==>
  (conditionally_orthogonal w b xs ys zs <=>
   !p x y z. ffs_prob_space w b p /\ x IN xs /\ y IN ys /\ z IN zs ==>
             prob p (x INTER z) * prob p (y INTER z) =
             prob p (x INTER y INTER z) * prob p z)
Proof
  strip_tac
  \\ eq_tac
  >- (
    rpt strip_tac
    \\ drule conditionally_orthogonal_imp_char_poly_factors
    \\ disch_then (drule_then (drule_then (drule_then drule)))
    \\ disch_then (mp_tac o Q.AP_TERM`flip (mpoly_eval Reals) (real o prob p)`)
    \\ simp[]
    \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_mul]
    \\ imp_res_tac factorises_FINITE
    \\ `FINITE z` by metis_tac[partitions_FINITE]
    \\ DEP_REWRITE_TAC[finite_mpoly_char_poly]
    \\ conj_asm1_tac >- metis_tac[INTER_FINITE, INTER_COMM]
    \\ simp[]
    \\ conj_tac >- simp[Reals_def]
    \\ drule_then drule ffs_prob_space_char_poly
    \\ disch_then(qspec_then`p`mp_tac)
    \\ impl_tac >- metis_tac[ffs_prob_space_def]
    \\ simp[]
    \\ disch_then(fn th => DEP_REWRITE_TAC[GSYM th])
    \\ conj_asm1_tac >- metis_tac[SUBSET_DEF, IN_INTER, partitions_thm]
    \\ simp[Reals_def]
    \\ `prob_space p` by fs[ffs_prob_space_def]
    \\ drule prob_normal
    \\ disch_then(fn th =>
         qspec_then`x INTER z`mp_tac th \\
         qspec_then`y INTER z`mp_tac th \\
         qspec_then`x INTER y INTER z`mp_tac th \\
         qspec_then`z`mp_tac th)
    \\ `events p = POW w` by fs[ffs_prob_space_def]
    \\ simp[IN_POW]
    \\ rpt strip_tac
    \\ gs[]
    \\ simp[extreal_mul_def]
    \\ metis_tac[realTheory.REAL_MUL_COMM] )
  \\ rpt strip_tac
  \\ Cases_on`w = {}` >- fs[factorises_empty, conditionally_orthogonal_def]
  \\ irule char_poly_factorises_imp_conditionally_orthogonal
  \\ simp[]
  \\ qx_genl_tac[`x`,`y`,`z`]
  \\ strip_tac
  \\ qexists_tac`char_poly b (x INTER y INTER z)`
  \\ imp_res_tac factorises_FINITE
  \\ `FINITE x /\ FINITE y /\ FINITE z`
  by metis_tac[partitions_FINITE]
  \\ conj_asm1_tac >- ( irule mpoly_char_poly \\ simp[] )
  \\ conj_asm1_tac >- simp[support_char_poly]
  \\ qmatch_goalsub_abbrev_tac`q1 = q2`
  \\ qmatch_asmsub_abbrev_tac`_ = mm p1 p2`
  \\ qmatch_asmsub_abbrev_tac`q1 = mm p3 p4`
  \\ qabbrev_tac`rr = mpoly_ring Reals (POW w)`
  \\ `p1 ∈ rr.carrier ∧ p2 ∈ rr.carrier ∧ p3 ∈ rr.carrier ∧ p4 ∈ rr.carrier`
  by (
    simp[Abbr`rr`, mpoly_ring_def]
    \\ unabbrev_all_tac
    \\ DEP_REWRITE_TAC[support_char_poly_SUBSET_POW]
    \\ simp[]
    \\ imp_res_tac partitions_thm
    \\ fs[SUBSET_DEF] )
  \\ `Ring rr` by simp[Abbr`rr`]
  \\ `q1 ∈ rr.carrier ∧ q2 ∈ rr.carrier`
  by (
    `mm = rr.prod.op` by simp[Abbr`rr`, mpoly_ring_def]
    \\ metis_tac[ring_mult_element] )
  \\ `ring_sub rr q2 q1 = rr.sum.id` suffices_by (
    DEP_ONCE_REWRITE_TAC[Q.SPEC`rr`ring_sub_eq_zero] \\ simp[] )
  \\ qmatch_goalsub_abbrev_tac`q = rr.sum.id`
  \\ `!f. IMAGE f (POW w) SUBSET { x | 0 < x } ==>
          mpoly_eval Reals q f = 0`
  by (
    rpt strip_tac
    \\ qabbrev_tac`pf = λe. mpoly_eval Reals (char_poly b e) f /
                            mpoly_eval Reals (char_poly b w) f`
    \\ `0 < mpoly_eval Reals (char_poly b w) f`
    by (
      rw[mpoly_eval_def]
      \\ DEP_REWRITE_TAC[GBAG_Reals_sum_BAG_IMAGE_BAG_OF_SET]
      \\ simp[]
      \\ irule real_sigmaTheory.REAL_SUM_IMAGE_SPOS
      \\ simp[PULL_EXISTS]
      \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
      \\ simp[ffs_poly_def, mono_bag_poly_def]
      \\ simp[BAG_OF_SET]
      \\ qx_gen_tac`v` \\ strip_tac
      \\ reverse IF_CASES_TAC >- metis_tac[]
      \\ simp[rrestrict_def]
      \\ simp[Once Reals_def]
      \\ simp[mono_bag_def]
      \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
      \\ conj_asm1_tac >- simp[]
      \\ simp[GBAG_Reals_prod_BAG_OF_SET]
      \\ irule iterateTheory.PRODUCT_POS_LT
      \\ simp[combinTheory.o_DEF]
      \\ fs[SUBSET_DEF, PULL_EXISTS]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ simp[IN_POW]
      \\ metis_tac[factorises_def, part_in_partition, partitions_thm] )
    \\ `∀e. e ⊆ w ⇒ 0 <= pf e`
    by (
      rpt strip_tac
      \\ simp[Abbr`pf`]
      \\ irule realTheory.REAL_LE_DIV
      \\ reverse conj_tac >- metis_tac[realTheory.REAL_LE_LT]
      \\ rw[mpoly_eval_def]
      \\ DEP_REWRITE_TAC[GBAG_Reals_sum_BAG_IMAGE_BAG_OF_SET]
      \\ `FINITE e` by metis_tac[SUBSET_FINITE]
      \\ simp[]
      \\ irule real_sigmaTheory.REAL_SUM_IMAGE_POS
      \\ simp[PULL_EXISTS]
      \\ simp[char_poly_def, mono_bag_poly_def]
      \\ qx_gen_tac`v` \\ strip_tac
      \\ simp[rrestrict_def]
      \\ reverse IF_CASES_TAC >- fs[Reals_def]
      \\ simp[Once Reals_def]
      \\ irule realTheory.REAL_LE_MUL
      \\ conj_tac >- simp[]
      \\ simp[mono_bag_def]
      \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
      \\ conj_asm1_tac >- simp[]
      \\ simp[GBAG_Reals_prod_BAG_OF_SET]
      \\ irule iterateTheory.PRODUCT_POS_LE
      \\ simp[combinTheory.o_DEF]
      \\ fs[SUBSET_DEF, PULL_EXISTS]
      \\ rpt strip_tac
      \\ simp[realTheory.REAL_LE_LT]
      \\ disj1_tac
      \\ first_x_assum irule
      \\ simp[IN_POW]
      \\ metis_tac[factorises_def, part_in_partition, partitions_thm] )
    \\ `pf {} = 0`
    by (
      simp[Abbr`pf`]
      \\ simp[Once char_poly_def]
      \\ simp[Once mpoly_eval_def, mono_bag_poly_def]
      \\ simp[Once Reals_def]
      \\ simp[realTheory.REAL_DIV_LZERO] )
    \\ `ffs_prob_space w b (w, POW w, Normal o pf)`
    by (
      simp[ffs_prob_space_def]
      \\ simp[p_space_def]
      \\ simp[events_def]
      \\ conj_asm1_tac
      >- (
        DEP_REWRITE_TAC[prob_on_finite_set]
        \\ simp[]
        \\ simp[positive_def, IN_POW]
        \\ conj_tac
        >- metis_tac[extreal_le_eq, extreal_of_num_def]
        \\ simp[prob_def, p_space_def]
        \\ conj_tac >- (
          simp[Abbr`pf`]
          \\ DEP_REWRITE_TAC[realTheory.REAL_DIV_REFL]
          \\ conj_tac >- (strip_tac \\ fs[])
          \\ metis_tac[extreal_le_eq, extreal_of_num_def] )
        \\ simp[additive_def, IN_POW]
        \\ rpt strip_tac
        \\ simp[extreal_add_eq]
        \\ simp[Abbr`pf`]
        \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
        \\ simp[]
        \\ conj_asm1_tac >- metis_tac[SUBSET_FINITE]
        \\ simp[Once ffs_poly_def]
        \\ DEP_REWRITE_TAC[BAG_OF_SET_DISJOINT_UNION]
        \\ simp[mono_bag_poly_BAG_UNION]
        \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_add]
        \\ simp[]
        \\ conj_tac
        >- (
          simp[finite_mpoly_def, PULL_EXISTS]
          \\ simp[Reals_def]
          \\ simp[mono_bag_def] )
        \\ conj_tac
        >- (
          fs[IN_DISJOINT]
          \\ metis_tac[mono_bag_inj, SUBSET_DEF] )
        \\ simp[Once Reals_def]
        \\ simp[GSYM ffs_poly_def]
        \\ simp[GSYM realTheory.REAL_DIV_ADD] )
      \\ qx_gen_tac`s` \\ strip_tac
      \\ simp[prob_def]
      \\ simp[combinTheory.o_DEF]
      \\ simp[GBAG_Reals_prod_BAG_OF_SET]
      \\ `∀x. x IN b ==> part x s =
             { chim w b {x} q r | (q,r) | q IN (part x s) /\ r IN w }`
      by (
        qx_gen_tac`u`
        \\ strip_tac
        \\ rewrite_tac[SET_EQ_SUBSET]
        \\ rewrite_tac[SUBSET_DEF]
        \\ `part u s IN u` by metis_tac[part_in_partition, factorises_def]
        \\ `u partitions w` by metis_tac[factorises_def]
        \\ `part u s SUBSET w` by metis_tac[partitions_thm]
        \\ conj_tac >- (
          qx_gen_tac`v`
          \\ strip_tac
          \\ qmatch_goalsub_abbrev_tac`chim w b uu _ _`
          \\ simp[]
          \\ qexistsl_tac[`v`,`v`]
          \\ DEP_REWRITE_TAC[chim_same]
          \\ simp[Abbr`uu`]
          \\ metis_tac[SUBSET_DEF] )
        \\ qmatch_goalsub_abbrev_tac`chim w b uu _ _`
        \\ simp[PULL_EXISTS]
        \\ qx_genl_tac[`v`,`r`]
        \\ strip_tac
        \\ `chim w b uu v r IN w` by metis_tac[chim_thm, SUBSET_DEF]
        \\ `part u s = part u (chim w b uu v r)`
        suffices_by metis_tac[in_part]
        \\ `u IN uu` by simp[Abbr`uu`]
        \\ `v IN w` by metis_tac[SUBSET_DEF]
        \\ drule chim_thm
        \\ disch_then(qspecl_then[`r`,`v`,`uu`]mp_tac)
        \\ impl_tac >- simp[] \\ strip_tac
        \\ first_x_assum drule
        \\ simp[] \\ strip_tac
        \\ irule part_unique
        \\ metis_tac[] )
      \\ `∀v. v IN b ==>
             mpoly_eval Reals (ffs_poly b (part v s)) f =
             mpoly_eval Reals (ffs_poly {v} (part v s)) f *
             mpoly_eval Reals (ffs_poly (b DELETE v) w) f`
      by (
        rpt strip_tac
        \\ drule_then drule ffs_poly_union_chim_mul
        \\ disch_then(qspecl_then[`w`,`part v s`,`b DELETE v`,`{v}`]mp_tac)
        \\ impl_keep_tac
        >- (
          simp[]
          \\ metis_tac[part_in_partition, partitions_thm, factorises_def] )
        \\ `{v} ∪ (b DELETE v) = b` by (simp[Once EXTENSION] \\ metis_tac[])
        \\ pop_assum SUBST1_TAC
        \\ qmatch_goalsub_abbrev_tac`ffs_poly b vw`
        \\ `vw = part v s`
        by (
          first_x_assum drule
          \\ disch_then SUBST1_TAC
          \\ simp[Abbr`vw`, Once EXTENSION, PULL_EXISTS, EXISTS_PROD] )
        \\ pop_assum SUBST1_TAC
        \\ disch_then SUBST1_TAC
        \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_mul]
        \\ reverse conj_tac >- simp[Once Reals_def]
        \\ conj_tac >- simp[]
        \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
        \\ `FINITE (part v s)` by metis_tac[SUBSET_FINITE]
        \\ simp[]
        \\ simp[support_ffs_poly, PULL_EXISTS]
        \\ simp[Reals_def] )
      \\ `∀v. v IN b ==>
             mpoly_eval Reals (ffs_poly b w) f =
             mpoly_eval Reals (ffs_poly {v} w) f *
             mpoly_eval Reals (ffs_poly (b DELETE v) w) f`
      by (
        rpt strip_tac
        \\ drule_then drule ffs_poly_union_chim_mul
        \\ disch_then(qspecl_then[`w`,`w`,`b DELETE v`,`{v}`]mp_tac)
        \\ impl_keep_tac >- simp[]
        \\ `{v} ∪ (b DELETE v) = b` by (simp[Once EXTENSION] \\ metis_tac[])
        \\ pop_assum SUBST1_TAC
        \\ qmatch_goalsub_abbrev_tac`ffs_poly b vw`
        \\ `vw = w`
        by (
          qunabbrev_tac`vw`
          \\ qmatch_goalsub_abbrev_tac`chim w b vv _ _`
          \\ simp[Once SET_EQ_SUBSET, SUBSET_DEF, PULL_EXISTS, EXISTS_PROD]
          \\ conj_tac >- metis_tac[chim_thm]
          \\ `vv ⊆ b` by simp[Abbr`vv`, SUBSET_DEF]
          \\ qx_gen_tac`u` \\ strip_tac
          \\ qexistsl_tac[`u`,`u`]
          \\ metis_tac[chim_same] )
        \\ pop_assum SUBST1_TAC
        \\ disch_then SUBST1_TAC
        \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_mul]
        \\ reverse conj_tac >- simp[Once Reals_def]
        \\ conj_tac >- simp[]
        \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
        \\ simp[]
        \\ simp[support_ffs_poly, PULL_EXISTS]
        \\ simp[Reals_def] )
      \\ `∀v. v IN b ==> mpoly_eval Reals (char_poly b (part v s)) f =
                         f (part v s) * mpoly_eval Reals (ffs_poly (b DELETE v) w) f`
      by (
        rpt strip_tac
        \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
        \\ simp[]
        \\ `v partitions w` by metis_tac[factorises_def]
        \\ `part v s IN v` by metis_tac[part_in_partition]
        \\ `part v s SUBSET w` by metis_tac[partitions_thm]
        \\ `FINITE (part v s)` by metis_tac[SUBSET_FINITE]
        \\ simp[]
        \\ disj2_tac
        \\ simp[ffs_poly_def]
        \\ `IMAGE (mono_bag {v}) (part v s) = {{|part v s|}}`
        by (
          simp[EXTENSION, PULL_EXISTS, mono_bag_def,
               BAG_OF_SET_INSERT_NON_ELEMENT]
          \\ reverse(rw[EQ_IMP_THM])
          >- metis_tac[in_part]
          \\ AP_THM_TAC \\ AP_TERM_TAC
          \\ irule EQ_SYM
          \\ irule part_unique
          \\ metis_tac[part_in_partition, SUBSET_DEF] )
        \\ pop_assum SUBST1_TAC
        \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
        \\ simp[mpoly_eval_def, BAG_OF_SET_INSERT_NON_ELEMENT]
        \\ simp[mono_bag_poly_sing]
        \\ simp[Reals_def, rrestrict_def] )
      \\ `∀v. v IN b ==> mpoly_eval Reals (char_poly b w) f =
                         mpoly_eval Reals (ffs_poly {v} w) f *
                         mpoly_eval Reals (ffs_poly (b DELETE v) w) f`
      by (
        rpt strip_tac
        \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
        \\ simp[]
        \\ `u partitions w` by metis_tac[factorises_def]
        \\ `part u s IN u` by metis_tac[part_in_partition]
        \\ `part u s SUBSET w` by metis_tac[partitions_thm]
        \\ `FINITE (part u s)` by metis_tac[SUBSET_FINITE]
        \\ simp[] )
      \\ `product b (λx. pf (part x s)) =
          product b (λx. f (part x s) / mpoly_eval Reals (ffs_poly {x} w) f)`
      by (
        irule iterateTheory.PRODUCT_EQ
        \\ simp[]
        \\ simp[Abbr`pf`]
        \\ qx_gen_tac`u` \\ strip_tac
        \\ first_x_assum drule
        \\ disch_then SUBST1_TAC
        \\ simp[]
        \\ qmatch_goalsub_abbrev_tac`r1 * r2 / (r3 * r2)`
        \\ DEP_REWRITE_TAC[realTheory.REAL_DIV_RMUL_CANCEL]
        \\ `0 < r2` suffices_by (rpt strip_tac \\ fs[])
        \\ qunabbrev_tac`r2`
        \\ simp[mpoly_eval_def]
        \\ simp[GBAG_Reals_sum_BAG_IMAGE_BAG_OF_SET]
        \\ irule real_sigmaTheory.REAL_SUM_IMAGE_SPOS
        \\ simp[PULL_EXISTS]
        \\ simp[rrestrict_def]
        \\ qx_gen_tac`v` \\ strip_tac
        \\ simp[Once Reals_def]
        \\ reverse IF_CASES_TAC >- fs[Reals_def]
        \\ irule realTheory.REAL_LT_MUL
        \\ simp[ffs_poly_def, mono_bag_poly_def]
        \\ simp[BAG_OF_SET]
        \\ reverse IF_CASES_TAC >- metis_tac[]
        \\ simp[]
        \\ simp[mono_bag_def]
        \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
        \\ simp[]
        \\ simp[GBAG_Reals_prod_BAG_OF_SET]
        \\ irule iterateTheory.PRODUCT_POS_LT
        \\ simp[]
        \\ fs[SUBSET_DEF,PULL_EXISTS]
        \\ rpt strip_tac \\ first_x_assum irule
        \\ simp[IN_POW]
        \\ metis_tac[part_in_partition, partitions_thm, factorises_def] )
      \\ pop_assum SUBST1_TAC
      \\ DEP_REWRITE_TAC[iterateTheory.PRODUCT_DIV]
      \\ simp[Abbr`pf`]
      \\ simp[Once mpoly_eval_def]
      \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
      \\ qmatch_goalsub_abbrev_tac`_ / xx = yy`
      \\ qmatch_goalsub_abbrev_tac`GBAG gg _`
      \\ simp[Reals_def]
      \\ simp_tac(srw_ss())[rrestrict_def]
      \\ qunabbrev_tac`gg`
      \\ simp[mono_bag_def, char_poly_def]
      \\ simp[BAG_OF_SET_INSERT_NON_ELEMENT]
      \\ simp[mono_bag_poly_def]
      \\ simp[mono_bag_def]
      \\ simp[BAG_INSERT, EMPTY_BAG]
      \\ `Reals.prod.op = $*` by simp[Reals_def]
      \\ pop_assum (fn th => simp[Once th])
      \\ simp[GSYM BAG_IMAGE_COMPOSE]
      \\ simp[GBAG_Reals_prod_BAG_OF_SET]
      \\ simp[combinTheory.o_DEF]
      \\ qunabbrev_tac`yy`
      \\ qunabbrev_tac`xx`
      \\ AP_TERM_TAC
      \\ DEP_REWRITE_TAC[char_poly_ffs_poly]
      \\ simp[]
      \\ DEP_ONCE_REWRITE_TAC[MP_CANON ffs_poly_decompose]
      \\ conj_tac >- simp[]
      \\ DEP_REWRITE_TAC[MP_CANON mpoly_eval_prod]
      \\ simp[]
      \\ conj_tac
      >- (
        simp[Abbr`rr`]
        \\ simp[mpoly_ring_def, Once SUBSET_DEF, PULL_EXISTS]
        \\ conj_asm1_tac
        >- (
          rw[]
          \\ irule support_ffs_poly_SUBSET_POW
          \\ simp[] \\ metis_tac[] )
        \\ simp[Once SUBSET_DEF, PULL_EXISTS]
        \\ simp[BAG_EVERY, PULL_EXISTS]
        \\ conj_tac >- rw[Reals_def]
        \\ rw[]
        \\ DEP_REWRITE_TAC[GSYM FINITE_support_finite_mpoly]
        \\ simp[]
        \\ metis_tac[SUBSET_FINITE, FINITE_POW] )
      \\ DEP_REWRITE_TAC[GSYM BAG_IMAGE_COMPOSE]
      \\ simp[]
      \\ DEP_REWRITE_TAC[GBAG_Reals_prod_BAG_OF_SET]
      \\ simp[combinTheory.o_DEF])
    \\ drule_then drule ffs_prob_space_char_poly
    \\ qmatch_asmsub_abbrev_tac`ffs_prob_space w b p`
    \\ disch_then(qspec_then`p`mp_tac)
    \\ impl_tac >- fs[ffs_prob_space_def]
    \\ simp[]
    \\ simp[Abbr`p`, combinTheory.o_DEF, prob_def]
    \\ srw_tac[boolSimps.ETA_ss][]
    \\ first_assum(qspec_then`x INTER z`mp_tac)
    \\ first_assum(qspec_then`y INTER z`mp_tac)
    \\ first_assum(qspec_then`x INTER y INTER z`mp_tac)
    \\ first_x_assum(qspec_then`z`mp_tac)
    \\ impl_keep_tac >- metis_tac[partitions_thm] \\ strip_tac
    \\ impl_tac >- fs[SUBSET_DEF] \\ strip_tac
    \\ impl_tac >- fs[SUBSET_DEF] \\ strip_tac
    \\ impl_tac >- fs[SUBSET_DEF] \\ strip_tac
    \\ ntac 4 (pop_assum mp_tac) \\ simp[]
    \\ rpt strip_tac
    \\ qmatch_asmsub_abbrev_tac`_ / nn`
    \\ `mpoly_eval Reals q2 f = pf (x INTER z) * nn * pf (y INTER z) * nn`
    by (
      qunabbrev_tac`pf`
      \\ simp_tac (srw_ss())[]
      \\ DEP_REWRITE_TAC[realTheory.REAL_DIV_RMUL]
      \\ conj_tac >- (strip_tac \\ fs[])
      \\ rewrite_tac[GSYM realTheory.REAL_MUL_ASSOC]
      \\ DEP_REWRITE_TAC[realTheory.REAL_DIV_RMUL]
      \\ conj_tac >- (strip_tac \\ fs[])
      \\ qunabbrev_tac`q2`
      \\ qunabbrev_tac`mm`
      \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_mul]
      \\ reverse conj_tac >- simp[Reals_def]
      \\ conj_tac >- simp[]
      \\ conj_tac >- simp[Abbr`p1`]
      \\ conj_tac >- simp[Abbr`p2`]
      \\ simp[Reals_def] )
    \\ `mpoly_eval Reals q1 f = pf z * nn * pf (x INTER y INTER z) * nn`
    by (
      qunabbrev_tac`pf`
      \\ simp_tac (srw_ss())[]
      \\ DEP_REWRITE_TAC[realTheory.REAL_DIV_RMUL]
      \\ conj_tac >- (strip_tac \\ fs[])
      \\ rewrite_tac[GSYM realTheory.REAL_MUL_ASSOC]
      \\ DEP_REWRITE_TAC[realTheory.REAL_DIV_RMUL]
      \\ conj_tac >- (strip_tac \\ fs[])
      \\ qunabbrev_tac`q1`
      \\ qunabbrev_tac`mm`
      \\ DEP_REWRITE_TAC[mpoly_eval_mpoly_mul]
      \\ reverse conj_tac >- simp[Reals_def]
      \\ conj_tac >- simp[]
      \\ conj_tac >- simp[Abbr`p3`]
      \\ conj_tac >- simp[Abbr`p4`]
      \\ simp[Reals_def] )
    \\ qunabbrev_tac`q`
    \\ qunabbrev_tac`rr`
    \\ DEP_REWRITE_TAC[mpoly_eval_sub]
    \\ conj_asm1_tac
    >- (
      fs[mpoly_ring_def]
      \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_POW]
      \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_POW]
      \\ simp[Reals_def] )
    \\ qhdtm_x_assum`mpoly_eval`SUBST1_TAC
    \\ qhdtm_x_assum`mpoly_eval`SUBST1_TAC
    \\ simp_tac(srw_ss())[Reals_sum_inv, Reals_def]
    \\ simp_tac(srw_ss())[Once realTheory.REAL_NEG_LMUL]
    \\ simp_tac(srw_ss())[GSYM realTheory.REAL_RDISTRIB]
    \\ Cases_on`nn = 0` >- simp[] \\ disj1_tac
    \\ simp_tac(srw_ss())[Once (GSYM realTheory.REAL_MUL_ASSOC)]
    \\ simp_tac(srw_ss())[Once realTheory.REAL_MUL_COMM]
    \\ simp_tac(srw_ss())[Once (GSYM realTheory.REAL_MUL_ASSOC), SimpR``realax$real_add``]
    \\ simp_tac(srw_ss())[Once realTheory.REAL_MUL_COMM, SimpR``realax$real_add``]
    \\ simp_tac(srw_ss())[Once realTheory.REAL_NEG_RMUL]
    \\ simp_tac(srw_ss())[GSYM realTheory.REAL_MUL_ASSOC]
    \\ simp_tac(srw_ss())[GSYM realTheory.REAL_LDISTRIB]
    \\ disj2_tac
    \\ ntac 4 (qpat_x_assum`pf _ = _`kall_tac)
    \\ simp_tac(srw_ss())[GSYM realTheory.REAL_NEG_RMUL]
    \\ rewrite_tac[GSYM realTheory.real_sub]
    \\ rewrite_tac[realTheory.REAL_SUB_0]
    \\ last_x_assum drule
    \\ disch_then drule
    \\ disch_then drule
    \\ disch_then drule
    \\ simp[prob_def]
    \\ simp[extreal_mul_def]
    \\ metis_tac[realTheory.REAL_MUL_COMM] )
  \\ `rr.sum.id = K Reals.sum.id`
  by simp[Abbr`rr`, mpoly_ring_def]
  \\ pop_assum SUBST1_TAC
  \\ irule zero_degree_of_is_zero
  \\ `q IN rr.carrier` by metis_tac[ring_sub_element]
  \\ `mpoly Reals q /\ support Reals q SUBSET POW w`
  by (
    pop_assum mp_tac
    \\ simp[Abbr`rr`, mpoly_ring_def] )
  \\ conj_tac >- metis_tac[SUBSET_FINITE, FINITE_POW]
  \\ conj_tac >- simp[]
  \\ reverse conj_tac >- simp[]
  \\ qexists_tac`K {x | 0 < x}`
  \\ simp[CONJ_ASSOC]
  \\ reverse conj_tac >- simp[Reals_def]
  \\ `INFINITE {x | 0r < x}`
  by (
    `1 IN {x | 0r < x}` by simp[]
    \\ `{x | 0r < x} <> {}` by metis_tac[MEMBER_NOT_EMPTY]
    \\ `open {x | 0r < x}` suffices_by metis_tac[real_topologyTheory.OPEN_IMP_INFINITE]
    \\ MATCH_ACCEPT_TAC real_topologyTheory.OPEN_INTERVAL_RIGHT )
  \\ simp[]
  \\ rpt strip_tac
  \\ simp[Once Reals_def, SimpRHS]
  \\ first_x_assum(qspec_then`λv. if v IN support Reals q then f v else 1`mp_tac)
  \\ impl_tac
  >- ( simp[SUBSET_DEF, PULL_EXISTS] \\ rw[] )
  \\ disch_then(SUBST1_TAC o SYM)
  \\ irule mpoly_eval_support
  \\ rw[]
QED

val _ = export_theory();
