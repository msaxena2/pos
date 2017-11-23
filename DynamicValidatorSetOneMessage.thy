(*
Copyright 2017 Yoichi Hirai

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

theory DynamicValidatorSetOneMessage

imports Main

begin

(* many things are copied and adjusted from @nano-o's contribution. *)

locale byz_quorums =
  -- "Here we fix two types @{typ 'q1} and @{typ 'q2} for quorums and one type @{typ 'v} for
      validator sets. of cardinality greater than 2/3 of 
the validators and quorum of cardinality greater than 1/3 of the validators."
  fixes member_1 :: "'n \<Rightarrow> 'q1 \<Rightarrow> 'v \<Rightarrow> bool" ("_ \<in>\<^sub>1 _ of _" 50)
    -- "Membership in 2/3 set"
    and member_2 :: "'n \<Rightarrow> 'q2 \<Rightarrow> 'v \<Rightarrow> bool" ("_ \<in>\<^sub>2 _ of _" 50)
    -- "Membership in 1/3 set"
  fixes
    hash_parent :: "'h \<Rightarrow> 'h \<Rightarrow> bool" (infix "\<leftarrow>" 50)
  fixes
    genesis :: 'h
  fixes
    vset_fwd :: "'h \<Rightarrow> 'v"
  fixes
    vset_bwd :: "'h \<Rightarrow> 'v"
  fixes
    vset_chosen :: "'h \<Rightarrow> 'v"
    -- "the next set chosen in the dynasity: https://ethresear.ch/t/casper-ffg-with-one-message-type-and-simpler-fork-choice-rule/103/34"
  assumes
  -- "Here we make assumptions about hashes. In reality any message containing a hash not satisfying those
should be dropped."
  -- "a hash has at most one parent which is not itself"
  "\<And> h1 h2 . h1 \<leftarrow> h2 \<Longrightarrow> h1 \<noteq> h2"
  and "\<And> h1 h2 h3 . \<lbrakk>h2 \<leftarrow> h1; h3 \<leftarrow> h1\<rbrakk> \<Longrightarrow> h2 = h3"
  and "\<And> q1 q2 vs. \<exists> q3 . \<forall> n . (n \<in>\<^sub>2 q3 of vs) \<longrightarrow> (n \<in>\<^sub>1 q1 of vs) \<and> (n \<in>\<^sub>1 q2 of vs)"  

    -- "This is the only property of types @{typ 'q1} and @{typ 'q2} that we need:
2/3 quorums have 1/3 intersection"

(* how do we get the forward and the backward validator set? *)
record ('n,'h)state =
  -- "@{typ 'n} is the type of validators (nodes), @{typ 'h} hashes, and views are @{typ nat}"
  -- "vote_msg node hash view view_src"
  vote_msg :: "'n \<Rightarrow> 'h \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"


locale casper = byz_quorums
begin

lemma hoge:
  "\<exists> q.  \<forall> n.  (n \<in>\<^sub>2 q of (vset_fwd root)) \<longrightarrow> ((n \<in>\<^sub>1 q0 of (vset_fwd root)) \<and> (n \<in>\<^sub>1 q1 of (vset_fwd root)))"
  using byz_quorums_axioms byz_quorums_def by force

inductive nth_parent where
  zeroth_parent: "nth_parent (0 :: nat) h h"
| Sth_parent: "nth_parent n oldest mid \<Longrightarrow> mid \<leftarrow> newest \<Longrightarrow> nth_parent (Suc n) oldest newest"

definition voted_by where
  "voted_by s q vset orig v2 h v1 \<equiv>
     v1 \<noteq> 0 \<and> v2 < v1 \<and> nth_parent (v1 - v2) orig h \<and>
     (\<forall> n. (n \<in>\<^sub>1 q of vset) \<longrightarrow> vote_msg s n h v1 v2)"

(* the forward set and the backward set must be taken from orig, not from h.
 * Otherwise, there is a forking situation.
 *)
definition voted_by_fwd where
  "voted_by_fwd s q orig v2 h v1 \<equiv>
     voted_by s q (vset_fwd h) orig v2 h v1"

definition voted_by_bwd where
  "voted_by_bwd s q orig v2 h v1 \<equiv>
     voted_by s q (vset_bwd h) orig v2 h v1"

definition voted_by_both where
  "voted_by_both s q0 q1 orig v2 h v1 \<equiv> voted_by_fwd s q0 orig v2 h v1 \<and> voted_by_bwd s q1 orig v2 h v1"

inductive hash_ancestor (infix "\<leftarrow>\<^sup>*" 50) where
  "h1 \<leftarrow> h2 \<Longrightarrow> h1 \<leftarrow>\<^sup>* h2"
| "\<lbrakk>h1 \<leftarrow> h2; h2 \<leftarrow>\<^sup>* h3\<rbrakk> \<Longrightarrow> h1 \<leftarrow>\<^sup>* h3"
declare hash_ancestor.intros[simp,intro]
lemma hash_ancestor_intro': assumes "h1 \<leftarrow>\<^sup>* h2" and "h2 \<leftarrow> h3" shows "h1 \<leftarrow>\<^sup>* h3" 
  using assms by (induct h1 h2 rule:hash_ancestor.induct) auto

lemma hash_ancestor_trans: assumes "h1 \<leftarrow>\<^sup>* h2" and "h2 \<leftarrow>\<^sup>* h3" shows "h1 \<leftarrow>\<^sup>* h3" 
  using assms by (induct h1 h2 rule:hash_ancestor.induct) auto

definition validator_changing_link where
"validator_changing_link s q0 q1 orig origE new newE \<equiv>
   voted_by_both s q0 q1 orig origE new newE \<and>
   vset_bwd new = vset_fwd orig \<and> vset_fwd new = vset_chosen orig"

definition usual_link where
"usual_link s q0 q1 orig origE new newE \<equiv>
   voted_by_both s q0 q1 orig origE new newE \<and>
   vset_bwd orig = vset_bwd new \<and> vset_fwd orig = vset_fwd new"

datatype Mode = Usual | FinalizingChild

inductive justified_with_root where
  justified_genesis: "r = r' \<Longrightarrow> rE = rE' \<Longrightarrow> justified_with_root r rE mode s r' rE' mode"
| usual_justification:
    "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new newE \<Longrightarrow>
     newM = (if newE - origE = 1 then FinalizingChild else Usual) \<Longrightarrow>
     justified_with_root r rE mode s new newE newM"
| justified_on_finalization:
   "justified_with_root r rE mode s c e FinalizingChild \<Longrightarrow>
    validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
    newM = (if ee - e = 1 then FinalizingChild else Usual) \<Longrightarrow>
    justified_with_root r rE mode s h ee newM"

inductive finalized_with_root where
  under_usual_link:
    "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new (origE + 1) \<Longrightarrow>
     finalized_with_root r rE mode s orig new origE Usual"
  | under_changing_link:
    "justified_with_root r rE mode s c e FinalizingChild \<Longrightarrow>
     validator_changing_link s q0 q1 c e h (e + 1) \<Longrightarrow>
     finalized_with_root r rE mode s c h e FinalizingChild"

abbreviation justified where
  "justified s h v m \<equiv> justified_with_root genesis 0 Usual s h v m"

definition fork where
  "fork s h0 v0 m0 h1 v1 m1 \<equiv> \<exists> child0 child1.
    (finalized_with_root genesis 0 Usual s h0 child0 v0 m0 \<and> finalized_with_root genesis 0 Usual s h1 child1 v1 m1 \<and>
     \<not>(h1 \<leftarrow>\<^sup>* h0 \<or> h0 \<leftarrow>\<^sup>* h1 \<or> h0 = h1))"

definition slashed_dbl where "slashed_dbl s n \<equiv>
  \<exists> h0 h1 v v0 v1. h0 \<noteq> h1 \<and> vote_msg s n h0 v v0 \<and> vote_msg s n h1 v v1"

definition slashed_surround where "slashed_surround s n \<equiv>
  \<exists> h0 h1 v0 v1 vs0 vs1. vs0 < vs1 \<and> vs1 < v1 \<and> v1 < v0
          \<and> vote_msg s n h0 v0 vs0 \<and> vote_msg s n h1 v1 vs1"

definition slashed where "slashed s n \<equiv> 
  slashed_dbl s n \<or> slashed_surround s n"

definition one_third_of_fwd_slashed where
"one_third_of_fwd_slashed s h q \<equiv>
  \<forall> n. (n \<in>\<^sub>2 q of (vset_fwd h)) \<longrightarrow> slashed s n"

definition one_third_of_bwd_slashed where
"one_third_of_bwd_slashed s h q \<equiv>
  \<forall> n. (n \<in>\<^sub>2 q of (vset_bwd h)) \<longrightarrow> slashed s n"

definition one_third_of_fwd_or_bwd_slashed where
"one_third_of_fwd_or_bwd_slashed s h q \<equiv>
   one_third_of_fwd_slashed s h q \<or> one_third_of_bwd_slashed s h q"


(**** intermediate stuff ends ****)

inductive justified_with_root_with_n_switchings where
  justified_genesis_n: "r = r' \<Longrightarrow> rE = rE' \<Longrightarrow> mode = mode' \<Longrightarrow>
     n = (0 :: nat) \<Longrightarrow>
     justified_with_root_with_n_switchings n r rE mode s r' rE' mode'"
| usual_justification_n:
    "justified_with_root_with_n_switchings n r rE mode s orig origE origM \<Longrightarrow>
     origM = Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new newE \<Longrightarrow>
     newM = (if newE - origE = 1 then FinalizingChild else Usual) \<Longrightarrow>
     justified_with_root_with_n_switchings n r rE mode s new newE newM"
| justified_on_finalization_n:
   "justified_with_root_with_n_switchings n r rE mode s c e origM \<Longrightarrow>
    origM = FinalizingChild \<Longrightarrow>
    validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
    newM = (if ee - e = 1 then FinalizingChild else Usual) \<Longrightarrow>
(*    newN = Suc n \<Longrightarrow> *)
    justified_with_root_with_n_switchings (Suc n) r rE mode s h ee newM"

lemma forget_n_switchings:
"justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
 justified_with_root r rE rM s h v m"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' s)
  then show ?case
    by (simp add: justified_genesis)
next
  case (usual_justification_n n r rE mode s orig origE q0 q1 new newE newM)
  then show ?case
    using casper.usual_justification casper_axioms by fastforce
next
  case (justified_on_finalization_n n r rE mode s c e q0 q1 h ee newM)
  then show ?case
    using casper.justified_on_finalization casper_axioms by fastforce
qed

lemma voted_by_higher:
  "voted_by s q vset orig v2 h v1 \<Longrightarrow>
   v2 < v1"
  by (simp add: voted_by_def)

lemma voted_by_fwd_higher:
  "voted_by_fwd s q orig v2 h v1 \<Longrightarrow>
   v2 < v1"
  by (simp add: voted_by_fwd_def voted_by_higher)

lemma voted_by_both_higher:
  "voted_by_both s q0 q1 orig v2 h v1 \<Longrightarrow>
   v2 < v1"
  using voted_by_both_def voted_by_fwd_higher by blast

lemma usual_link_higher:
  "usual_link s q0 q1 orig origE new newE \<Longrightarrow>
   origE < newE"
  using usual_link_def voted_by_both_higher by blast

lemma validator_changing_link_higher:
    "validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
     e < ee"
  using validator_changing_link_def voted_by_both_higher by blast

lemma voted_by_fwd_means_ancestor :
  "voted_by_fwd s q orig v2 h v1 \<Longrightarrow>
   nth_parent (v1 - v2) orig h"
  by (simp add: voted_by_def voted_by_fwd_def)

lemma voted_by_both_means_ancestor:
  "voted_by_both s q0 q1 orig v2 h v1 \<Longrightarrow>
  nth_parent (v1 - v2) orig h"
  using voted_by_both_def voted_by_fwd_means_ancestor by blast

lemma validator_changing_link_means_ancestor:
   "validator_changing_link s q0 q1 c e h ee \<Longrightarrow>
    nth_parent (ee - e) c h"
  using validator_changing_link_def voted_by_both_means_ancestor by blast

lemma justifies_higher:
  "justified_with_root r rE rM s h v m \<Longrightarrow>
   rE \<le> v"
proof(induct rule: justified_with_root.induct)
  case (justified_genesis r rE s)
  then show ?case by simp
next
  case (usual_justification r rE s orig origE q0 q1 new newE)
  then show ?case
    by (meson casper.usual_link_higher casper_axioms leD leI order.strict_trans)
next
  case (justified_on_finalization r rE s c e q0 q1 h ee)
  then show ?case
    by (meson leD leI less_trans validator_changing_link_higher)
qed

lemma justified_with_root_refl:
  "justified_with_root h v m s h v m"
  by (simp add: justified_genesis)

lemma justified_with_root_trans:
   "justified_with_root h1 v1 m1 s h2 v2 m2 \<Longrightarrow>
    justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
    justified_with_root h0 v0 m0 s h2 v2 m2"
proof(induct rule: justified_with_root.inducts)
  case (justified_genesis r r' rE rE' s)
  then show ?case by blast
next
  case (usual_justification r rE s orig origE q0 q1 new newE)
  then show ?case
    using justified_with_root.usual_justification by blast
next
  case (justified_on_finalization r rE s c e q0 q1 h ee)
  then show ?case
    using casper.justified_on_finalization casper_axioms by fastforce
qed


inductive finalized_with_root_with_n_switchings where
  under_usual_link_n:
    "justified_with_root_with_n_switchings n r rE mode s orig origE Usual \<Longrightarrow>
     usual_link s q0 q1 orig origE new (origE + 1) \<Longrightarrow>
     finalized_with_root_with_n_switchings n r rE mode s orig new origE Usual"
  | under_changing_link_n:
    "justified_with_root_with_n_switchings n r rE mode s c e FinalizingChild \<Longrightarrow>
     validator_changing_link s q0 q1 c e h (e + 1) \<Longrightarrow>
     finalized_with_root_with_n_switchings n r rE mode s c h e FinalizingChild"

lemma fjn:
  "finalized_with_root_with_n_switchings n r rE rM s h child v m \<Longrightarrow>
   justified_with_root_with_n_switchings n r rE rM s h v m"
proof(induct rule: finalized_with_root_with_n_switchings.induct)
  case (under_usual_link_n n r rE mode s orig origE q0 q1 new)
  then show ?case
    by linarith
next
  case (under_changing_link_n n r rE mode s c e q0 q1 h)
  then show ?case
    by simp
qed


definition close_finalization where
  "close_finalization s r rE rM h v m \<equiv>
  (rE + 1 < v \<longrightarrow> m = Usual) \<and>
   ((\<exists> child.
    finalized_with_root_with_n_switchings (0 :: nat) r rE rM s h child v m) \<or>
  (\<exists> child. finalized_with_root_with_n_switchings (1 :: nat) r rE rM s h child v m) \<and> rE < v \<and> (rE + 1 = v \<longrightarrow> vset_fwd h = vset_chosen r \<and> rM = FinalizingChild) \<or>
  (\<exists> child. finalized_with_root_with_n_switchings (2 :: nat) r rE rM s h child v m) \<and> rE + 1 < v \<and> vset_bwd h = vset_chosen r \<and> rM = FinalizingChild)"

definition close_justification where
  "close_justification s r rE rM h v hist \<equiv>
  (rE + 1 < v \<longrightarrow> hist = Usual) \<and>
  (justified_with_root_with_n_switchings (0 :: nat) r rE rM s h v hist \<or>
  justified_with_root_with_n_switchings (1 :: nat) r rE rM s h v hist \<and> rE < v \<and> (rE + 1 = v \<longrightarrow> vset_fwd h = vset_chosen r \<and> rM = FinalizingChild) \<or>
  justified_with_root_with_n_switchings (2 :: nat) r rE rM s h v hist \<and> rE + 1 < v \<and> vset_bwd h = vset_chosen r \<and> rM = FinalizingChild)"

definition justification_fork_with_root where
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 \<equiv>
     justified s r rE rM \<and>
     (\<exists> child0 child1.
       finalized_with_root r rE rM s h0 child0 v0 m0 \<and> finalized_with_root r rE rM s h1 child1 v1 m1) \<and>
    \<not>(justified_with_root h1 v1 m1 s h0 v0 m0 \<or> justified_with_root h0 v0 m0 s h1 v1 m1)"

lemma justification_fork_with_root_sym :
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 =
   justification_fork_with_root s r rE rM h1 v1 m1 h0 v0 m0"
  by (meson justification_fork_with_root_def)

definition small_fork where
  "small_fork s hr vr mr h0 v0 m0 h1 v1 m1 \<equiv>
    justification_fork_with_root s hr vr mr h0 v0 m0 h1 v1 m1 \<and>
    (\<forall> hr' vr' mr' h0' v0' m0' h1' v1' m1'.
       v0' + v1' - vr' < v0 + v1 - vr \<longrightarrow>
       \<not> justification_fork_with_root s hr' vr' mr' h0' v0' m0' h1' v1' m1')"

lemma small_fork_sym :
  "small_fork s hr vr mr h0 v0 m0 h1 v1 m1 = small_fork s hr vr mr h1 v1 m1 h0 v0 m0"
  by (simp add: add.commute justification_fork_with_root_sym small_fork_def)

lemma close_justification_refl:
  "close_justification s r rE rM r rE rM"
  by (simp add: close_justification_def justified_genesis_n)

lemma justified_graft :
   "justified s r rE rM \<Longrightarrow>
    justified_with_root r rE rM s h v m \<Longrightarrow>
    justified s h v m"
  using justified_with_root_trans by blast

lemma usual_link_means_ancestor:
 "usual_link s q0 q1 orig origE new newE \<Longrightarrow>
  nth_parent (newE - origE) orig new"
  by (meson casper.usual_link_def casper.voted_by_both_means_ancestor casper_axioms)

lemma nth_parent_trans:
  "nth_parent b mid fin \<Longrightarrow>
   nth_parent a orig mid \<Longrightarrow>
   nth_parent (a + b) orig fin"
proof(induct rule: nth_parent.induct)
case (zeroth_parent h)
  then show ?case
    by simp
next
  case (Sth_parent n oldest mid newest)
  then show ?case
    using nth_parent.Sth_parent by auto
qed

lemma justified_means_ancestor:
  "justified_with_root r rE rM s h v m \<Longrightarrow>
   nth_parent (v - rE) r h"
proof(induct rule: justified_with_root.induct)
  case (justified_genesis r r' rE rE' mode s)
  then show ?case
    by (simp add: zeroth_parent)
next
  case (usual_justification r rE mode s orig origE q0 q1 new newE)
  then show ?case
  proof -
    have "nth_parent (origE - rE + (newE - origE)) r new"
      using local.usual_justification(2) local.usual_justification(3) nth_parent_trans usual_link_means_ancestor by blast
    then show ?thesis
      by (metis Nat.add_diff_assoc add.commute casper.justifies_higher casper_axioms le_add_diff_inverse2 less_imp_le_nat local.usual_justification(3) usual_justification.hyps(1) usual_link_higher)
  qed
next
  case (justified_on_finalization r rE mode s c e q0 q1 h ee)
  then show ?case
  proof -
have f1: "nth_parent (e - rE + (ee - e)) r h"
by (meson casper.validator_changing_link_means_ancestor casper_axioms justified_on_finalization.hyps(2) justified_on_finalization.hyps(3) nth_parent_trans)
  have f2: "rE \<le> e"
    by (meson casper.justifies_higher casper_axioms justified_on_finalization.hyps(1))
  have "e < ee"
    by (meson casper.validator_changing_link_higher casper_axioms justified_on_finalization.hyps(3))
  then show ?thesis
    using f2 f1 by (metis (no_types) Nat.add_diff_assoc add.commute le_add_diff_inverse2 less_imp_le_nat)
qed
qed

lemma nth_parent_unique:
   "nth_parent n r0 h \<Longrightarrow>
    nth_parent n r1 h \<Longrightarrow>
    r0 = r1"
proof(induct n arbitrary: h)
  case 0
  then show ?case
    by (metis less_numeral_extra(3) nth_parent.simps zero_less_Suc)
next
  case (Suc n)
  obtain mid0 where m0: "nth_parent n r0 mid0 \<and> mid0 \<leftarrow> h"
    using Suc.prems(1) nth_parent.simps by blast
  obtain mid1 where m1: "nth_parent n r1 mid1 \<and> mid1 \<leftarrow> h"
    using Suc.prems(2) nth_parent.simps by blast
  have u: "mid0 = mid1"
    by (metis byz_quorums_axioms byz_quorums_def m0 m1)
  then show ?case
    using Suc.hyps m0 m1 by blast
qed


lemma justified_back_unique:
   "justified_with_root r0 rE rM s h v m \<Longrightarrow>
    justified_with_root r1 rE rM s h v m \<Longrightarrow>
    r0 = r1"
  using justified_means_ancestor nth_parent_unique by blast

lemma finalized_is_justified :
  "finalized_with_root r rE rM s h c v m \<Longrightarrow>
   justified_with_root r rE rM s h v m"
  by(auto simp add: finalized_with_root.simps)

lemma when_n_justified_is_justified:
  "finalized_with_root r rE rM s h c v m \<Longrightarrow>
   justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
   finalized_with_root_with_n_switchings n r rE rM s h c v m"
proof(induct rule: finalized_with_root.cases)
  case (under_usual_link r rE mode s orig origE q0 q1 new)
  then show ?case
    by (meson casper.under_usual_link_n casper_axioms)
next
  case (under_changing_link r rE mode s c e q0 q1 h)
  then show ?case
    by (meson casper.under_changing_link_n casper_axioms)
qed


lemma jf :
  "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
   finalized_with_root r rE rM s h c v m \<Longrightarrow>
   \<exists> child. finalized_with_root_with_n_switchings n r rE rM s h child v m"
  by (meson casper.when_n_justified_is_justified casper_axioms)


lemma when_close_justification_is_finalized_f :
  "close_justification s r rE FinalizingChild h v m \<Longrightarrow>
   finalized_with_root r rE FinalizingChild s h c v m \<Longrightarrow>
   close_finalization s r rE FinalizingChild h v m"
  by(auto simp add: close_finalization_def close_justification_def jf)

lemma when_close_justification_is_finalized_u :
  "close_justification s r rE Usual h v m \<Longrightarrow>
   finalized_with_root r rE Usual s h c v m \<Longrightarrow>
   close_finalization s r rE Usual h v m"
  by(auto simp add: close_finalization_def close_justification_def jf)

lemma when_close_justification_is_finalized :
  "close_justification s r rE rM h v m \<Longrightarrow>
   finalized_with_root r rE rM s h c v m \<Longrightarrow>
   close_finalization s r rE rM h v m"
  apply(cases rM)
   apply (simp add: when_close_justification_is_finalized_u)
  by (simp add: when_close_justification_is_finalized_f)

lemma small_fork_has_no_middle_fin:
 "justified s r rE rM \<Longrightarrow>
    finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
    finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   rE \<noteq> v0' \<Longrightarrow> v0' \<noteq> v0 \<Longrightarrow>
   justified_with_root r rE rM s h0' v0' m0' \<Longrightarrow>
   justified_with_root h0' v0' m0' s h0 v0 m0 \<Longrightarrow> \<not> finalized_with_root r rE rM s h0' c0' v0' m0'"
  sorry

lemma not_finalizing:
  "origM \<noteq> FinalizingChild \<Longrightarrow> origM = Usual"
  using Mode.exhaust by blast

lemma justified_with_shallow_usual_link:
  "justified_with_root_with_n_switchings n r rE mode s orig origE Usual \<Longrightarrow>
   usual_link s q0 q1 orig origE new newE \<Longrightarrow>
   newE - origE = 1 \<Longrightarrow>
   finalized_with_root r rE mode s orig new origE Usual"
proof -
  assume num: "newE - origE = 1"
  assume "justified_with_root_with_n_switchings n r rE mode s orig origE Usual"
  then have "justified_with_root r rE mode s orig origE Usual"
    using forget_n_switchings by blast
  moreover have "newE = origE + 1"
    using num by linarith
  moreover assume "usual_link s q0 q1 orig origE new newE"
  ultimately show ?thesis
    using under_usual_link by blast
qed

lemma finalizing_can_happen_near:
  "justified_with_root_with_n_switchings n r rE rM s c e m \<Longrightarrow>
   m = FinalizingChild \<Longrightarrow>
   \<forall> h' c' v' m'.
      rE \<noteq> v' \<longrightarrow> v' \<noteq> e \<longrightarrow>
      justified_with_root r rE rM s h' v' m' \<longrightarrow>
      justified_with_root h' v' m' s c e FinalizingChild \<longrightarrow>
      \<not> finalized_with_root r rE rM s h' c' v' m' \<Longrightarrow>
   e \<le> rE + 1"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' s)
  then show ?case by linarith
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have f :"finalized_with_root r rE mode s orig new origE Usual"
    using casper.justified_with_shallow_usual_link casper_axioms usual_justification_n.hyps(1)
         usual_justification_n.hyps(3) usual_justification_n.hyps(4) usual_justification_n.hyps(5)
         usual_justification_n.prems(1) by fastforce
  show ?case proof(cases "rE = origE")
    case True
    then show ?thesis
      by (metis Mode.simps(1) add_diff_inverse_nat eq_iff less_numeral_extra(3)
           nat_diff_split usual_justification_n.hyps(4) usual_justification_n.hyps(5)
           usual_justification_n.prems(1) usual_link_higher zero_less_diff)
  next
    case False
    have diff1: "rE \<noteq> origE"
      by (simp add: False)
    have diff2: "origE \<noteq> newE"
      using usual_justification_n.hyps(5) usual_justification_n.prems(1) by force
    have j1: "justified_with_root r rE mode s orig origE Usual"
      using f finalized_is_justified by blast
    have j2: "justified_with_root orig origE Usual s new newE FinalizingChild"
      using casper.justified_with_root_refl casper_axioms usual_justification
         usual_justification_n.hyps(4) usual_justification_n.hyps(5)
         usual_justification_n.prems(1) by fastforce
    have "\<forall>h' c' v' m'.
       rE \<noteq> v' \<longrightarrow>
       v' \<noteq> newE \<longrightarrow>
       justified_with_root r rE mode s h' v' m' \<longrightarrow>
       justified_with_root h' v' m' s new newE newM \<longrightarrow>
       \<not> finalized_with_root r rE mode s h' c' v' m'"
      using usual_justification_n.prems by blast
    moreover have "newM = FinalizingChild"
      by (simp add: usual_justification_n.prems(1))
    ultimately have r: "rE \<noteq> origE \<Longrightarrow> origE \<noteq> newE \<Longrightarrow>
      justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
      justified_with_root orig origE Usual s new newE FinalizingChild \<Longrightarrow>
      \<not> finalized_with_root r rE mode s orig new origE Usual"
      by blast
    have strange: " \<not> finalized_with_root r rE mode s orig new origE Usual"
      using diff1 diff2 j1 j2 by(rule r; auto)
    show ?thesis using f strange by auto
  qed
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  have f :"finalized_with_root r rE mode s c h e FinalizingChild"
    by (metis Mode.simps(1) add_diff_inverse_nat casper.under_changing_link casper_axioms 
       forget_n_switchings justified_on_finalization_n.hyps(1)
       justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(4)
       justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(1) less_numeral_extra(3)
       nat_diff_split validator_changing_link_higher zero_less_diff)
  have "e = rE"
    by (metis casper.finalized_is_justified casper.justified_with_root.intros(3) casper_axioms f justified_genesis justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(1) justified_on_finalization_n.prems(2) nat_neq_iff validator_changing_link_higher)
  then show ?case
    by (metis Mode.simps(1) add_diff_inverse_nat eq_iff
      justified_on_finalization_n.hyps(4) justified_on_finalization_n.hyps(5)
      justified_on_finalization_n.prems(1) less_numeral_extra(3) 
      nat_diff_split validator_changing_link_higher zero_less_diff)
qed

lemma justified_switch_really_higher :
  "justified_with_root_with_n_switchings n r rE mode s h ee m \<Longrightarrow>
   0 < n \<Longrightarrow>
   rE < ee"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (meson less_trans usual_link_higher)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (meson casper.justifies_higher casper_axioms forget_n_switchings less_le_trans linorder_not_le validator_changing_link_higher)
qed

lemma short_one_switching:
"justified_with_root_with_n_switchings one r rE mode s h ee FinalizingChild \<Longrightarrow>
 one = (1 :: nat) \<Longrightarrow>
 rE + 1 = ee \<Longrightarrow>
 vset_fwd h = vset_chosen r"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' s)
  then show ?case
    by linarith
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have "rE = origE"
    using justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_link_higher by fastforce
  then have "False"
    using casper.justified_switch_really_higher casper_axioms usual_justification_n.hyps(1) usual_justification_n.prems(1) by fastforce
  then show ?case by simp
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have "validator_changing_link s q0 q1 r rE h ee"
    by (metis One_nat_def add.right_neutral add_Suc_right casper.justifies_higher casper_axioms forget_n_switchings justified_means_ancestor le_neq_implies_less neq0_conv not_less_eq nth_parent_unique validator_changing_link_higher zero_less_diff zeroth_parent)
  then show ?case
    using validator_changing_link_def by blast
qed

lemma refl_inv:
 "justified_with_root_with_n_switchings n r rE mode s c e origM \<Longrightarrow>
  rE = e \<Longrightarrow>
  origM = mode"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case  by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (metis casper.justifies_higher casper_axioms diff_is_0_eq' forget_n_switchings less_numeral_extra(3) usual_link_higher zero_less_diff)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (metis casper.justifies_higher casper_axioms diff_is_0_eq' forget_n_switchings less_numeral_extra(3) validator_changing_link_higher zero_less_diff)
qed

lemma short_fin:
"justified_with_root_with_n_switchings one r rE mode s h ee FinalizingChild \<Longrightarrow>
 one = (1 :: nat) \<Longrightarrow>
 rE + 1 = ee \<Longrightarrow>
 mode = FinalizingChild"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case
  by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  have "rE = origE"
    using justified_switch_really_higher usual_justification_n.hyps(1) usual_justification_n.hyps(4) usual_justification_n.prems(1) usual_justification_n.prems(2) usual_link_higher by fastforce
  then have "False"
    using casper.justified_switch_really_higher casper_axioms usual_justification_n.hyps(1) usual_justification_n.prems(1) by fastforce
  then show ?case by simp
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have "e = rE"
    by (metis One_nat_def Suc_diff_Suc add.right_neutral add_Suc_right casper.justifies_higher casper_axioms diff_Suc_Suc diff_add_inverse2 diff_diff_cancel diff_is_0_eq forget_n_switchings order.strict_iff_order validator_changing_link_higher)
  then show ?case
    using justified_on_finalization_n.hyps(1) justified_on_finalization_n.hyps(3) justified_on_finalization_n.hyps(5) justified_on_finalization_n.prems(2) refl_inv by fastforce
qed


lemma jR':
   "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
    usual_link s q0 q1 orig origE new newE \<Longrightarrow>
    newE - origE = 1 \<Longrightarrow>
    finalized_with_root r rE mode s orig new origE Usual"
  by (metis le_add_diff_inverse less_imp_le under_usual_link usual_link_higher)

lemma jR:
   "justified_with_root r rE mode s orig origE Usual \<Longrightarrow>
    usual_link s q0 q1 orig origE new newE \<Longrightarrow>
    newM = (if newE - origE = 1 then FinalizingChild else Usual) \<Longrightarrow>
    \<forall>h' c' v' m'.
       rE \<noteq> v' \<longrightarrow>
       v' \<noteq> newE \<longrightarrow>
       justified_with_root r rE mode s h' v' m' \<longrightarrow>
       justified_with_root h' v' m' s new newE newM \<longrightarrow> \<not> finalized_with_root r rE mode s h' c' v' m' \<Longrightarrow>
    rE + 1 < newE \<Longrightarrow> newE - origE \<noteq> 1"
proof(cases "newE - origE = 1")
  case True
  assume j0: "justified_with_root r rE mode s orig origE Usual"
  assume u: " usual_link s q0 q1 orig origE new newE"
  then have "finalized_with_root r rE mode s orig new origE Usual"
    using True j0 jR' by blast
  assume strech: "rE + 1 < newE"
  have dif0: "rE \<noteq> origE"
    using True strech by linarith
  have dif1: "origE \<noteq> newE"
    using True by linarith
  assume "newM = (if newE - origE = 1 then FinalizingChild else Usual)"
  then have nF: "newM = FinalizingChild"
    by (simp add: True)
  have j1: "justified_with_root orig origE Usual s new newE FinalizingChild"
    by (meson True casper.justified_genesis casper_axioms u usual_justification)
  have j2: "justified_with_root orig origE Usual s new newE newM"
    by (simp add: j1 nF)
  assume no_mid: "\<forall>h' c' v' m'.
       rE \<noteq> v' \<longrightarrow>
       v' \<noteq> newE \<longrightarrow>
       justified_with_root r rE mode s h' v' m' \<longrightarrow>
       justified_with_root h' v' m' s new newE newM \<longrightarrow> \<not> finalized_with_root r rE mode s h' c' v' m'"
  then have "\<not> finalized_with_root r rE mode s orig new origE Usual"
    using dif0 dif1 j0 j2 by blast
  then show ?thesis
    using \<open>finalized_with_root r rE mode s orig new origE Usual\<close> by blast
next
  case False
  then show ?thesis by blast
qed

lemma close_justification_alt :
  "justified_with_root r rE rM s h v m \<Longrightarrow>
   \<forall> h' c' v' m'.
      rE \<noteq> v' \<longrightarrow> v' \<noteq> v \<longrightarrow>
      justified_with_root r rE rM s h' v' m' \<longrightarrow>
      justified_with_root h' v' m' s h v m \<longrightarrow> \<not> finalized_with_root r rE rM s h' c' v' m' \<Longrightarrow>
   close_justification s r rE rM h v m"
proof(induct rule: justified_with_root.induct)
  case (justified_genesis r r' rE rE' mode s)
  then show ?case by (simp add: close_justification_refl)
next
  case (usual_justification r rE mode s orig origE q0 q1 new newE newM)
  then have cd: "rE + 1 < newE \<longrightarrow> newE - origE \<noteq> 1"
    using jR by blast
  then have c0: "rE + 1 < newE \<longrightarrow> newM = Usual"
    by (simp add: usual_justification.hyps(4))
  have "close_justification s r rE mode orig origE Usual"
    by (smt antisym justified_with_root.usual_justification justifies_higher order.order_iff_strict usual_justification.hyps(2) usual_justification.hyps(3) usual_justification.hyps(4) usual_justification.prems usual_link_higher)
  then consider 
    (a) "justified_with_root_with_n_switchings (0 :: nat) r rE mode s orig origE Usual" |
    (b) "justified_with_root_with_n_switchings (1 :: nat) r rE mode s orig origE Usual \<and> rE < origE \<and> (rE + 1 = origE \<longrightarrow> vset_fwd orig = vset_chosen r \<and> mode = FinalizingChild)" |
    (c) "justified_with_root_with_n_switchings (2 :: nat) r rE mode s orig origE Usual \<and> rE + 1 < origE \<and> vset_bwd orig = vset_chosen r \<and> mode = FinalizingChild"
    using close_justification_def by blast
  then show ?case proof(cases)
    case a
    then show ?thesis
      by (smt casper.close_justification_def casper.usual_justification_n casper_axioms cd usual_justification.hyps(3) usual_justification.hyps(4))
  next
    case b
    then show ?thesis
      by (smt Suc_eq_plus1 Suc_leI c0 casper.usual_justification_n casper_axioms cd close_justification_def justifies_higher le_less_trans nat_neq_iff usual_justification.hyps(1) usual_justification.hyps(3) usual_link_higher)
  next
    case c
    then show ?thesis
      by (smt casper.usual_justification_n casper_axioms cd close_justification_def le_less_trans order.strict_iff_order usual_justification.hyps(3) usual_justification.hyps(4) usual_link_def usual_link_higher)
  qed

  next
  case (justified_on_finalization r rE mode s c e q0 q1 h ee newM)
  then have "close_justification s r rE mode c e FinalizingChild"
  proof -
    obtain nn :: nat and eea :: 'e and mm :: Mode and eeb :: 'e where
      "(\<exists>v0 v1 v2 v3. (rE \<noteq> v2 \<and> v2 \<noteq> e \<and> justified_with_root r rE mode s v0 v2 v3 \<and> justified_with_root v0 v2 v3 s c e FinalizingChild) \<and> finalized_with_root r rE mode s v0 v1 v2 v3) = ((rE \<noteq> nn \<and> nn \<noteq> e \<and> justified_with_root r rE mode s eea nn mm \<and> justified_with_root eea nn mm s c e FinalizingChild) \<and> finalized_with_root r rE mode s eea eeb nn mm)"
      by blast
    moreover
    { assume "justified_with_root eea nn mm s h ee (if ee - e = 1 then FinalizingChild else Usual)"
      moreover
      { assume "\<not> nn \<le> ee \<or> nn = ee"
        then have "(rE = nn \<or> nn = e \<or> \<not> justified_with_root r rE mode s eea nn mm \<or> \<not> justified_with_root eea nn mm s c e FinalizingChild) \<or> \<not> finalized_with_root r rE mode s eea eeb nn mm"
          by (meson justifies_higher le_less_trans local.justified_on_finalization(3) order.strict_iff_order validator_changing_link_higher) }
      ultimately have "(rE = nn \<or> nn = e \<or> \<not> justified_with_root r rE mode s eea nn mm \<or> \<not> justified_with_root eea nn mm s c e FinalizingChild) \<or> \<not> finalized_with_root r rE mode s eea eeb nn mm"
        using justified_on_finalization.hyps(4) justified_on_finalization.prems by blast }
    ultimately show ?thesis
      using justified_with_root.justified_on_finalization local.justified_on_finalization(2) local.justified_on_finalization(3) by blast
  qed
  then consider (a) "justified_with_root_with_n_switchings (0 :: nat) r rE mode s c e FinalizingChild" |
    (b) "justified_with_root_with_n_switchings (1 :: nat) r rE mode s c e FinalizingChild \<and> rE < e \<and> (rE + 1 = e \<longrightarrow> vset_fwd c = vset_chosen r)" |
    (c) "justified_with_root_with_n_switchings (2 :: nat) r rE mode s c e FinalizingChild \<and> rE + 1 < e \<and> vset_bwd c = vset_chosen r \<and> mode = FinalizingChild"
    by(simp add: close_justification_def; auto)
  then show ?case proof cases
    case a
    then show ?thesis proof (cases "ee = e + 1")
      case True
      have nextj: "justified_with_root_with_n_switchings (1 :: nat) r rE mode s h ee FinalizingChild"
        using True a casper.justified_with_root_with_n_switchings.intros(3) casper_axioms justified_on_finalization.hyps(3) by fastforce
      have ee_big: "rE < ee"
        using casper.justifies_higher casper_axioms justified_on_finalization.hyps(1) justified_on_finalization.hyps(3) nat.simps(3) validator_changing_link_higher by fastforce
      have additional: "rE + 1 = ee \<longrightarrow> vset_fwd h = vset_chosen r \<and> mode = FinalizingChild"
        using nextj short_fin short_one_switching by blast
      have "justified_with_root_with_n_switchings (1 :: nat) r rE mode s h ee FinalizingChild \<and> rE < ee \<and> (rE + 1 = ee \<longrightarrow> vset_fwd h = vset_chosen r \<and> mode = FinalizingChild)"
        using additional ee_big nextj by linarith
      then show ?thesis
        by (smt One_nat_def Suc_diff_Suc Suc_eq_plus1 True cancel_comm_monoid_add_class.diff_cancel casper.close_justification_def casper_axioms finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justified_on_finalization.prems leD validator_changing_link_higher)
    next
      case False
      then show ?thesis
        by (smt One_nat_def Suc_eq_plus1 Suc_lessI a add_diff_inverse_nat casper.justified_with_root_with_n_switchings.intros(3) casper_axioms close_justification_def justified_on_finalization.hyps(1) justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justifies_higher le_less_trans le_neq_implies_less less_numeral_extra(3) nat_diff_split validator_changing_link_higher zero_less_diff)
    qed
  next
    case b
    then show ?thesis
    proof(cases "ee - e = 1")
      case True
      have j2: "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee FinalizingChild"
      proof -
        have "\<forall>x0 x10 x11 x12 x13 x14 x16 x1 x4 x6 x7 x8 x9. casper.justified_with_root_with_n_switchings (x16::'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) x14 x13 x12 x11 (Suc x10) x9 x8 x7 (x6::(_, 'e, 'f) state_scheme) x1 x0 (if x0 - x4 = 1 then FinalizingChild else Usual) = (if x0 - x4 = 1 then casper.justified_with_root_with_n_switchings x16 x14 x13 x12 x11 (Suc x10) x9 x8 x7 x6 x1 x0 FinalizingChild else casper.justified_with_root_with_n_switchings x16 x14 x13 x12 x11 (Suc x10) x9 x8 x7 x6 x1 x0 Usual)"
          by presburger
        then have "justified_with_root_with_n_switchings (Suc 1) r rE mode s h ee FinalizingChild"
          by (meson True b casper.justified_with_root_with_n_switchings.intros(3) casper_axioms justified_on_finalization.hyps(3))
        then show ?thesis
          by (metis Suc_1)
      qed
      have num: "rE + 1 < ee"
        using True b by linarith
      have "rE < e"
        by (simp add: b)
      moreover have "e \<le> rE + 1"
        by (smt True finalizing_can_happen_near j2 justified_on_finalization.hyps(4) justified_on_finalization.prems leD num)
      ultimately have era: "rE + 1 = e"
        by linarith
      have "vset_bwd h = vset_fwd c"
        using justified_on_finalization.hyps(3) validator_changing_link_def by blast
      moreover have "vset_fwd c = vset_chosen r" (* I need the fact rE + 1 = e ... Maybe strengthen the close_justification conditions? *)
        using b era by blast
      ultimately have vs: "vset_bwd h = vset_chosen r"
        by simp
      have "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee FinalizingChild \<and> rE + 1 < ee \<and> vset_bwd h = vset_chosen r"
        using j2 num vs by blast
      then show ?thesis
        by (smt True finalizing_can_happen_near justified_on_finalization.hyps(4) justified_on_finalization.prems leD)
    next
      case False
      have "validator_changing_link s q0 q1 c e h ee"
        using justified_on_finalization.hyps(3) by auto
      have jee: "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee Usual"
        by (metis False One_nat_def b casper.justified_with_root_with_n_switchings.intros(3) casper_axioms justified_on_finalization.hyps(3) numeral_2_eq_2)
      moreover have "rE < ee"
        by (meson b justified_on_finalization.hyps(3) less_trans validator_changing_link_higher)
      moreover have "rE + 1 \<noteq> ee"
        using b justified_on_finalization.hyps(3) validator_changing_link_higher by fastforce
      ultimately have "justified_with_root_with_n_switchings (2 :: nat) r rE mode s h ee Usual \<and> rE + 1 < ee \<and> vset_bwd h = vset_chosen r"
        by (smt antisym b casper.justified_with_root.intros(3) casper_axioms diff_is_0_eq' discrete finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justified_on_finalization.prems justifies_higher less_numeral_extra(3) validator_changing_link_def validator_changing_link_higher zero_less_diff)
      moreover have "newM = Usual"
        using False justified_on_finalization.hyps(4) by auto
      moreover have "mode = FinalizingChild"
        by (smt False Suc_eq_plus1 Suc_lessI b calculation(2) finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.prems justified_with_root.justified_on_finalization justifies_higher not_less short_fin validator_changing_link_higher)
      ultimately show ?thesis
        by (simp add: close_justification_def)
    qed
  next
    case c
    then show ?thesis
      by (smt finalizing_can_happen_near justified_on_finalization.hyps(3) justified_on_finalization.hyps(4) justified_on_finalization.prems justified_with_root.justified_on_finalization justifies_higher leD validator_changing_link_higher)
  qed
qed

lemma close_finalization_alt :
  "finalized_with_root r rE rM s h c v m \<Longrightarrow>
   \<forall> h' c' v' m'.
      rE \<noteq> v' \<longrightarrow> v' \<noteq> v \<longrightarrow>
      justified_with_root r rE rM s h' v' m' \<longrightarrow>
      justified_with_root h' v' m' s h v m \<longrightarrow> \<not> finalized_with_root r rE rM s h' c' v' m' \<Longrightarrow>
   close_finalization s r rE rM h v m"
  by (simp add: close_justification_alt finalized_is_justified when_close_justification_is_finalized)

lemma close_justification_three:
 "justified s r rE rM \<Longrightarrow>
    finalized_with_root r rE rM s h0 child0 v0 m0 \<Longrightarrow>
    finalized_with_root r rE rM s h1 child1 v1 m1 \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
proof -
  assume "justified s r rE rM"
  moreover assume f0: "finalized_with_root r rE rM s h0 child0 v0 m0"
  moreover assume "finalized_with_root r rE rM s h1 child1 v1 m1"
  moreover assume "\<not> justified_with_root h1 v1 m1 s h0 v0 m0"
  moreover assume "\<not> justified_with_root h0 v0 m0 s h1 v1 m1"
  moreover assume "\<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'"
  ultimately have "\<forall> h0' c0' v0' m0'.
      rE \<noteq> v0' \<longrightarrow> v0' \<noteq> v0 \<longrightarrow> justified_with_root r rE rM s h0' v0' m0' \<longrightarrow> 
      justified_with_root h0' v0' m0' s h0 v0 m0 \<longrightarrow> \<not> finalized_with_root r rE rM s h0' c0' v0' m0'"
    apply(rule_tac allI)
    apply(rule_tac allI)
    apply(rule_tac allI)
    apply(rule_tac allI)
    apply(rule_tac impI)
    apply(rule_tac impI)
    apply(rule_tac impI)
    apply(rule_tac impI)
    by(rule small_fork_has_no_middle_fin; auto)
  then show ?thesis
    using close_finalization_alt f0 by blast
qed

lemma close_justification_two:
 "justified s r rE rM \<Longrightarrow>
    (\<exists>child0. finalized_with_root r rE rM s h0 child0 v0 m0) \<Longrightarrow>
    (\<exists>child1. finalized_with_root r rE rM s h1 child1 v1 m1) \<Longrightarrow>
    \<not> justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow> \<not> justified_with_root h0 v0 m0 s h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
proof -
  assume j: "justified s r rE rM"
  assume "\<exists>child0. finalized_with_root r rE rM s h0 child0 v0 m0"
  then obtain child0 where a0: "finalized_with_root r rE rM s h0 child0 v0 m0" by blast
  assume "\<exists>child1. finalized_with_root r rE rM s h1 child1 v1 m1"
  then obtain child1 where a1: "finalized_with_root r rE rM s h1 child1 v1 m1" by blast
  assume a2: "\<not> justified_with_root h1 v1 m1 s h0 v0 m0"
  assume a3: "\<not> justified_with_root h0 v0 m0 s h1 v1 m1"
  assume a4: "
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'"
  show ?thesis using j a0 a1 a2 a3 a4 by(rule close_justification_three; auto)
qed

lemma close_justification_one:
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<forall>r' rE' rM' h0' v0' m0' h1' v1' m1'.
      v0' + v1' - rE' < v0 + v1 - rE \<longrightarrow> \<not> justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1' \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
  apply (simp add: justification_fork_with_root_def)
  apply (rule_tac close_justification_two; auto)
  apply (auto simp add: justification_fork_with_root_def)
  by blast

lemma small_fork_has_close_justification :
  "small_fork s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   close_finalization s r rE rM h0 v0 m0"
  apply(simp add: small_fork_def)
  apply(rule close_justification_one; auto)
  by blast

lemma close_justification_era:
  "close_justification s r rE rM h v m \<Longrightarrow>
   rE \<le> v"
  by (meson casper.close_justification_def casper_axioms forget_n_switchings justifies_higher)

lemma close_justification_is_justification:
  "close_justification s r rE rM h v m \<Longrightarrow>
   justified_with_root r rE rM s h v m"
  by (meson casper.close_justification_def casper_axioms forget_n_switchings justifies_higher)

lemma trivial_is_refl0:
  "justified_with_root_with_n_switchings 0 r v rM s h v m \<Longrightarrow> rE = v \<Longrightarrow> r = h"
  by (metis cancel_comm_monoid_add_class.diff_cancel forget_n_switchings justified_means_ancestor less_Suc_eq_0_disj less_numeral_extra(3) nth_parent.simps)

lemma trivial_is_refl1:
  "justified_with_root_with_n_switchings 0 r v rM s h v m \<Longrightarrow> rE = v \<Longrightarrow> rM = m"
  using refl_inv by blast

lemma trivial_is_refl:
  "close_justification s r rE rM h v m \<Longrightarrow>
   rE = v \<Longrightarrow>
   r = h \<and> rM = m"
  by (metis casper.close_justification_def casper_axioms not_add_less1 order_less_irrefl refl_inv trivial_is_refl0)

lemma really_close_justification_zero:
  "justified_with_root_with_n_switchings n r rE rM s h rE' m \<Longrightarrow>
   rE' = Suc rE \<Longrightarrow> m = FinalizingChild"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case using n_not_Suc_n by blast
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (metis Nat.diff_diff_right Suc_eq_plus1_left casper.forget_n_switchings casper.usual_link_higher casper_axioms diff_is_0_eq' justifies_higher linorder_not_le minus_nat.diff_0 not_less_eq_eq)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
then show ?case
  by (metis Suc_eq_plus1 add_left_imp_eq casper.justifies_higher casper_axioms forget_n_switchings leD le_add_diff_inverse not_less_eq_eq order.strict_iff_order validator_changing_link_higher)
qed

lemma close_justification_mode_f:
  "close_justification s r rE rM h v m \<Longrightarrow>
   v = rE + 1 \<Longrightarrow> m = FinalizingChild"
  by (metis Suc_eq_plus1 casper.close_justification_def casper_axioms really_close_justification_zero)

lemma close_justification_mode_u:
  "close_justification s r rE rM h v m \<Longrightarrow>
   v > rE + 1 \<Longrightarrow> m = Usual"
  by(auto simp add: close_justification_def)

lemma zero_switching_means:
  "justified_with_root_with_n_switchings n r rE Usual s h0 v m0 \<Longrightarrow>
   n = 0 \<Longrightarrow>
   vset_fwd r = vset_fwd h0 \<and>
   vset_bwd r = vset_bwd h0"
proof(induct rule: justified_with_root_with_n_switchings.induct)
  case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (simp add: usual_link_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case by linarith
qed

lemma one_switching_means:
  "justified_with_root_with_n_switchings n r rE rM s h0 v m0 \<Longrightarrow>
   rM = Usual \<Longrightarrow>
   n = Suc 0 \<Longrightarrow>
   vset_fwd r = vset_bwd h0"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (simp add: usual_link_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then have "justified_with_root_with_n_switchings 0 r rE Usual s c e origM"
    by blast
  then have e1: "vset_fwd r = vset_fwd c"
    using zero_switching_means by blast
  have "vset_fwd c = vset_bwd h"
    using justified_on_finalization_n.hyps(4) validator_changing_link_def by force
  then show ?case
    by (simp add: e1)
qed



lemma justified_is_voted:
   "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
    rE \<noteq> v \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_fwd h) p0 pv0 h v"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
  then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case by (meson usual_link_def voted_by_both_def voted_by_fwd_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (meson casper.validator_changing_link_def casper.voted_by_both_def casper_axioms voted_by_fwd_def)
qed

lemma justified_is_voted_bwd:
   "justified_with_root_with_n_switchings n r rE rM s h v m \<Longrightarrow>
    rE \<noteq> v \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_bwd h) p0 pv0 h v"
proof(induct rule: justified_with_root_with_n_switchings.induct)
case (justified_genesis_n r r' rE rE' mode mode' n s)
then show ?case by simp
next
  case (usual_justification_n n r rE mode s orig origE origM q0 q1 new newE newM)
  then show ?case
    by (meson usual_link_def voted_by_both_def voted_by_bwd_def)
next
  case (justified_on_finalization_n n r rE mode s c e origM q0 q1 h ee newM)
  then show ?case
    by (meson validator_changing_link_def voted_by_both_def voted_by_bwd_def)
qed


lemma zero_switching_involves_root_vote:
   "rE \<noteq> v \<Longrightarrow>
    justified_with_root_with_n_switchings 0 r rE Usual s h0 v m0 \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
proof -
  assume j: "justified_with_root_with_n_switchings 0 r rE Usual s h0 v m0"
  have same: "vset_fwd r = vset_fwd h0"
    using j zero_switching_means by blast
  assume non_trivial: "rE \<noteq> v"
  have v: "\<exists>q0 p0 pv0. voted_by s q0 (vset_fwd h0) p0 pv0 h0 v"
    by (meson casper.justified_is_voted casper_axioms j non_trivial)
  show ?thesis
    by (simp add: same v)
qed

lemma one_switching_involves_root_vote:
   "rE \<noteq> v \<Longrightarrow>
    justified_with_root_with_n_switchings (Suc 0) r rE Usual s h0 v m0 \<Longrightarrow>
    \<exists>q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
proof -
  assume j: "justified_with_root_with_n_switchings (Suc 0) r rE Usual s h0 v m0"
  have same: "vset_fwd r = vset_bwd h0"
    using j one_switching_means by blast
  assume non_trivial: "rE \<noteq> v"
  have v: "\<exists>q0 p0 pv0. voted_by s q0 (vset_bwd h0) p0 pv0 h0 v"
    using j justified_is_voted_bwd non_trivial by blast
  show ?thesis
    by (simp add: same v)
qed

lemma close_involves_vote:
  "close_justification s r rE Usual h0 v m0 \<Longrightarrow>
   rE \<noteq> v \<Longrightarrow>
   \<exists> q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
  by (metis Mode.simps(1) One_nat_def casper.close_justification_def casper_axioms one_switching_involves_root_vote zero_switching_involves_root_vote)

lemma double_vote:
  "voted_by s q0 vset p0 pv0 h0 v \<Longrightarrow>
   voted_by s q1 vset p1 pv1 h1 v \<Longrightarrow>
   h0 \<noteq> h1 \<Longrightarrow>
   \<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> slashed s n"
proof -
  assume v0: "voted_by s q0 vset p0 pv0 h0 v"
  assume v1: "voted_by s q1 vset p1 pv1 h1 v"
  have "\<exists> q. \<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> (n \<in>\<^sub>1 q0 of vset) \<and> (n \<in>\<^sub>1 q1 of vset)"
    by (metis byz_quorums_axioms byz_quorums_def)
  then obtain q where qP: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> (n \<in>\<^sub>1 q0 of vset) \<and> (n \<in>\<^sub>1 q1 of vset)"
    by blast
  have vv0: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> vote_msg s n h0 v pv0"
    using qP v0 voted_by_def by blast
  have vv1: "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> vote_msg s n h1 v pv1"
    using qP v1 voted_by_def by blast
  assume diff: "h0 \<noteq> h1"
  have ddr: "\<forall> n. vote_msg s n h0 v pv0 \<longrightarrow> vote_msg s n h1 v pv1 \<longrightarrow> slashed_dbl s n"
    using diff slashed_dbl_def by fastforce
  have "\<forall> n. (n \<in>\<^sub>2 q of vset) \<longrightarrow> slashed_dbl s n"
    by (simp add: ddr vv0 vv1)
  then show ?thesis
    by (meson slashed_def)
qed


lemma close_finalizations_cause_slashing_u_j :
  " close_justification s r rE Usual h0 v m0 \<Longrightarrow>
    close_justification s r rE Usual h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
    \<exists>q. one_third_of_fwd_or_bwd_slashed s r q"
proof -
  assume c0: "close_justification s r rE Usual h0 v m0"
  assume c1: "close_justification s r rE Usual h1 v m1"
  assume n01: "\<not> justified_with_root h0 v m0 s h1 v m1"
  then have not_same: "h0 \<noteq> h1 \<or> m0 \<noteq> m1"
    using justified_genesis by blast
  have non_trivial: "rE \<noteq> v"
    using c0 c1 not_same trivial_is_refl by blast
  have v0: "\<exists> q0 p0 pv0. voted_by s q0 (vset_fwd r) p0 pv0 h0 v"
    using c0 close_involves_vote non_trivial by blast
  have v1: "\<exists> q1 p1 pv1. voted_by s q1 (vset_fwd r) p1 pv1 h1 v"
    using c1 close_involves_vote non_trivial by blast
  have "m0 = m1"
    by (metis c0 c1 close_justification_era close_justification_mode_f close_justification_mode_u discrete le_neq_implies_less non_trivial)
  then have "h0 \<noteq> h1"
    using not_same by blast
  then show ?thesis
    by (meson casper.double_vote casper_axioms one_third_of_fwd_or_bwd_slashed_def one_third_of_fwd_slashed_def v0 v1)
qed

lemma close_fj :
  "close_finalization s r rE rM h v m \<Longrightarrow>
   close_justification s r rE rM h v m"
  by(auto simp add: close_finalization_def close_justification_def fjn)

lemma close_finalizations_cause_slashing_u_inner :
  " close_finalization s r rE Usual h0 v m0 \<Longrightarrow>
    close_finalization s r rE Usual h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
    \<exists>q. one_third_of_fwd_or_bwd_slashed s r q"
  by (meson casper.close_finalizations_cause_slashing_u_j casper.close_fj casper_axioms)

lemma close_finalizations_cause_slashing_u :
  " close_finalization s r rE Usual h0 v m0 \<Longrightarrow>
    close_finalization s r rE Usual h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  using close_finalizations_cause_slashing_u_inner by blast

lemma close_finalizations_cause_slashing_f :
  " close_finalization s r rE FinalizingChild h0 v m0 \<Longrightarrow>
    close_finalization s r rE FinalizingChild h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
    \<exists>q r'. (\<exists>rE'. Ex (justified s r' rE')) \<and> one_third_of_fwd_or_bwd_slashed s r' q"
(* harder than the usual case, maybe *)
  sorry

(* after child, it must rotate *)
lemma close_finalizations_cause_slashing :
  "close_finalization s r rE rM h0 v m0 \<Longrightarrow>
   close_finalization s r rE rM h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h0 v m0 s h1 v m1 \<Longrightarrow>
   \<not> justified_with_root h1 v m1 s h0 v m0 \<Longrightarrow>
   justified s r rE rM \<Longrightarrow>
   \<exists> q r' rE' rM'. justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
  apply(cases rM; clarsimp)
   apply (simp add: close_finalizations_cause_slashing_u)
  by (simp add: close_finalizations_cause_slashing_f)

lemma small_accountable_safety_equal :
  "small_fork s r rE rM h0 v m0 h1 v m1 \<Longrightarrow>
   \<exists> q r' rE' rM' . justified s r' rE' rM' \<and> one_third_of_fwd_or_bwd_slashed s r' q"
proof -
  assume a: "small_fork s r rE rM h0 v m0 h1 v m1"
  have dif0: "\<not> justified_with_root h0 v m0 s h1 v m1"
    using a casper.justification_fork_with_root_def casper.small_fork_def casper_axioms by fastforce
  have dif1: "\<not> justified_with_root h1 v m1 s h0 v m0"
    using a casper.small_fork_def casper_axioms justification_fork_with_root_def by fastforce
  have c0: "close_finalization s r rE rM h0 v m0"
    by (meson a casper.small_fork_has_close_justification casper_axioms)
  have c1: "close_finalization s r rE rM h1 v m1"
    using a small_fork_has_close_justification small_fork_sym by blast
  have j: "justified s r rE rM"
    using a casper.small_fork_def casper_axioms justification_fork_with_root_def by fastforce
  show ?thesis
    using dif0 dif1 c0 c1 j close_finalizations_cause_slashing by blast
qed

lemma small_accountable_safety_gt :
  "small_fork s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   v0 > v1 \<Longrightarrow>
   \<exists> h v m q. justified s h v m \<and> one_third_of_fwd_or_bwd_slashed s h q"
  sorry (* this one is the harder case, so leave it until _equal is done *)

lemma small_accountable_safety :
  "small_fork s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> h v m q. justified s h m v \<and> one_third_of_fwd_or_bwd_slashed s h q"
proof(cases "v0 = v1")
  case True
  moreover assume "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
  ultimately have "small_fork s r rE rM h0 v1 m0 h1 v1 m1" by simp
  then show ?thesis
    using small_accountable_safety_equal by blast
next
  case False
  moreover assume a: "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
  then have b: "small_fork s r rE rM h1 v1 m1 h0 v0 m0"
    by (simp add: justification_fork_with_root_def small_fork_def)
  consider "v0 > v1" | "v1 > v0"
    using calculation nat_neq_iff by blast
  then show ?thesis
  using a b proof cases
    case 1
    then show ?thesis
      using a small_accountable_safety_gt by blast
  next
    case 2
    then show ?thesis
      using b small_accountable_safety_gt by blast
  qed
qed


lemma justification_fork_to_small:
  "justification_fork_with_root s r rE rM h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> r' rE' rM' h0' v0' m0' h1' v1' m1'.
     small_fork s r' rE' rM' h0' v0' m0' h1' v1' m1'"
proof(induct "v0 + v1 - rE" arbitrary: r rE rM h0 v0 m0 h1 v1 m1 rule: less_induct)
  case less
  then show ?case
  proof (cases "\<exists> r' rE' rM' h0' v0' m0' h1' v1' m1'. v0' + v1' - rE' < v0 + v1 - rE \<and>
                justification_fork_with_root s r' rE' rM' h0' v0' m0' h1' v1' m1'")
    case True
    then show ?thesis
      using less.hyps by blast
  next
    case False
    then have "small_fork s r rE rM h0 v0 m0 h1 v1 m1"
      by (simp add: less.prems small_fork_def)
    then show ?thesis by blast
  qed
qed

lemma justification_accountable_safety :
  "justification_fork_with_root s genesis 0 Usual h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> h v m q. justified s h v m \<and> one_third_of_fwd_or_bwd_slashed s h q"
  using casper.small_accountable_safety casper_axioms justification_fork_to_small by fastforce

lemma nth_parent_is_ancestor:
  "nth_parent n orig h \<Longrightarrow>
   orig \<leftarrow>\<^sup>* h \<or> orig = h"
proof(induct rule: nth_parent.induct)
  case (zeroth_parent h)
  then show ?case
    by simp
next
  case (Sth_parent n oldest mid newest)
  then show ?case
    using hash_ancestor_intro' by blast
qed

lemma voted_by_both_connects_ancestor_descendant:
  "voted_by_both s q0 q1 orig origE new newE \<Longrightarrow>
   orig \<leftarrow>\<^sup>* new \<or> orig = new"
  by (meson casper.voted_by_both_def casper_axioms nth_parent_is_ancestor voted_by_bwd_def)

lemma usual_link_connects_ancestor_descendant:
  "usual_link s q0 q1 orig origE new newE \<Longrightarrow>
   orig \<leftarrow>\<^sup>* new \<or> orig = new"
  using usual_link_def voted_by_both_connects_ancestor_descendant by blast

lemma justification_is_ancestor:
  "justified_with_root h1 v1 m1 s h0 v0 m0 \<Longrightarrow>
   h1 \<leftarrow>\<^sup>* h0 \<or> h1 = h0"
proof(induct rule:justified_with_root.induct)
  case (justified_genesis r rE s)
  then show ?case
    by simp
next
  case (usual_justification r rE s orig origE q0 q1 new newE)
  then show ?case
    using hash_ancestor_trans usual_link_connects_ancestor_descendant by blast
next
  case (justified_on_finalization r rE s p e q0 q1 c h ee)
  then show ?case
    by (metis hash_ancestor_trans validator_changing_link_def voted_by_both_connects_ancestor_descendant)
qed


lemma fork_to_justification_fork_with_root:
  "fork s h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   justification_fork_with_root s genesis 0 Usual h0 v0 m0 h1 v1 m1"
  by (metis fork_def justification_fork_with_root_def justification_is_ancestor justified_genesis)

(** intermediate stuff ends here **)

lemma accountable_safety :
  "fork s h0 v0 m0 h1 v1 m1 \<Longrightarrow>
   \<exists> h v m q. justified s h v m \<and> one_third_of_fwd_or_bwd_slashed s h q"
  using fork_to_justification_fork_with_root justification_accountable_safety by blast

end

section "Definitions Necessary to Understand Accountable Safety (not skippable)"

subsection "Hashes, Views and Validators"

text "In this development we do not know much about hashes.  There are many hashes.
Two hashes might be equal or not.  The intention is that the hashes identify blocks but we don't
have to talk about that."

datatype hash = Hash int

text "Views are numbers.  We actually need the fact that views are lines up in a total order.
Otherwise accountable safety can be broken.  We sometimes subtract views and obtain a number.
So, for convenience, views are just defined as integers.  Of course when we are multiplying a view
by a view, that would be very strange."

type_synonym view = int

text "We have two kinds of messages.  A Commit message contains a hash and a view,
indicating that a hash is to be finalized at a view.  Many signatures on this message would
actually finalize the hash at the view.
A prepare message contains a hash and two views.
At this point a message is not signed by anybody."

datatype message =
  Commit "hash * view"
| Prepare "hash * view * view"

text "We need a set of validators.  Here, we just define a datatype containing infinitely many
validators.
Afterwards, when we look at a particular situation, each hash would specify two validator sets."

datatype validator = Validator int

text "A message signed by a validator can be represented as a pair of a validator and a message."

type_synonym signed_message = "validator * message"

text "Almost everything in this document depends on situations.  A situation contains a set of
signed messages, two validator sets for each hash, and a function specifying parents of hashes."

text "A situation might be seen from a global point of view where every sent messages can be seen,
or more likely seen from a local point of view."

record situation =
  RearValidators :: "hash \<Rightarrow> validator set"
  FwdValidators :: "hash \<Rightarrow> validator set"
  Messages :: "signed_message set"
  PrevHash :: "hash \<Rightarrow> hash option"

text "
The accountable safety will make sure that at least one-third of the validators are slashed.
In Isabelle/HOL, the cardinality of an infinite set is defined to be zero, so we will avoid that
because it does not make sense to divide the cardinality of an infinite set by three.
We should be talking
about situations where the set of validators is finite.
At the same time, we assume that the validator sets are not empty (I haven't tried to remove the
non-emptiness assumption)."

definition validator_sets_finite :: "situation \<Rightarrow> bool"
  where "validator_sets_finite s = (\<forall> h. finite (FwdValidators s h) \<and>
                                         finite (RearValidators s h) \<and>
                                         (\<not> (FwdValidators s h = {})) \<and>
                                         (\<not> (RearValidators s h = {})))"

text "A hash's previous hash's previous hash is a second-ancestor.  Later, we will see that an honest
validator will send a prepare message only after seeing enough prepare messages for the ancestor of a
particular degree.  So we need to define what is the ancestor of a particular degree."

fun nth_ancestor :: "situation \<Rightarrow> nat \<Rightarrow> hash \<Rightarrow> hash option"
where
  "nth_ancestor _ 0 h = Some h"
| "nth_ancestor s (Suc n) h =
   (case PrevHash s h of
      None \<Rightarrow> None
    | Some h' \<Rightarrow> nth_ancestor s n h')"

text "When hashes are connected by @{term nth_ancestor} relation,
they are in ancestor-descendant relation."

definition ancestor_descendant :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"ancestor_descendant s x y = (\<exists> n. nth_ancestor s n y = Some x)"

text "When two hashes are in ancestor-descendant relation in any ordering,
they are on the same chain."

definition on_same_chain :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where "on_same_chain s x y = (ancestor_descendant s x y \<or> ancestor_descendant s y x)"

subsection "When Hashes are Prepared and Committed"

text "Blocks can be finalized only when two-thirds of the validators commit on the block.
Also, in the slashing conditions, we will be talking about two-thirds of the validators doing
something."

text "We can lift any predicate about a validator into a predicate about a set of validators:
that two thirds of the validators satisfy the predicate."

definition two_thirds :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"two_thirds vs f =
   (2 * card vs \<le> 3 * card ({n. n \<in> vs \<and> f n}))"

text "Similarly for one-third, more-than-two-thirds, and more-than-one-third."

definition one_third :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"one_third vs f =
   (card vs \<le> 3 * card ({n. n \<in> vs \<and> f n}))"

text "It matters when two-thirds of validators say something."

definition two_thirds_sent_message :: "situation \<Rightarrow> validator set \<Rightarrow> message \<Rightarrow> bool"
where
"two_thirds_sent_message s vs m =
   two_thirds vs (\<lambda> n. (n, m) \<in> Messages s)"

text "A hash is prepared when two-thirds of the validators have sent a Prepare message
with the same content."

definition prepared :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared s vs h v vsrc =
   (two_thirds_sent_message s vs (Prepare (h, v, vsrc)))"


text "A hash is committed when two-thirds of the validators have sent a Commit message
with the same content."

definition committed :: "situation \<Rightarrow> validator set \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed s vs h v = two_thirds_sent_message s vs (Commit (h, v))"

text "As we will see, honest validators should send a prepare message only when
it has enough prepare messages at a particular view.  Those prepare messages need
to be signed by two-thirds of both the rear and the forward validators."

text "A hash at a view and a view source is prepared by the rear validators when
two-thirds of the rear validators have signed the prepare message."

definition prepared_by_rear :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_rear s h v vsrc =
   (prepared s (RearValidators s h) h v vsrc)"

text "Similarly for the forward validators."

definition prepared_by_fwd :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_fwd s h v vsrc =
   (prepared s (FwdValidators s h) h v vsrc)"

text "When both of these happens, a prepare is signed by both the rear and the forward validator sets."

definition prepared_by_both :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> view \<Rightarrow> bool"
where
"prepared_by_both s h v vsrc =
  (prepared_by_rear s h v vsrc \<and> prepared_by_fwd s h v vsrc)"

text "Similar definitions for commit messages."

definition committed_by_rear :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_rear s h v =
   (committed s (RearValidators s h) h v)"

definition committed_by_fwd :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_fwd s h v =
   (committed s (FwdValidators s h) h v)"

definition committed_by_both :: "situation \<Rightarrow> hash \<Rightarrow> view \<Rightarrow> bool"
where
"committed_by_both s h v =
   (committed_by_rear s h v \<and> committed_by_fwd s h v)"


subsection "Following Changing Validators to Define Forks"

text "In the accountable safety statement, we need to slash 2/3 of a set of validators.
This set of validators cannot be any set, but some legitimately chosen descendant of the
first sets of validators.  We need to look at the history and see what validator set
inherits the seats.
For this, we need to see the sourcing relation of pepare messages."

text "The sourcing relation is also used in a slashing condition."

text "One type of prepare source is the normal one.  The normal source needs to have the same 
rear validator set and the same forward validator set."

definition validators_match :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_match s h0 h1 =
  (RearValidators s h0 = RearValidators s h1 \<and>
   FwdValidators s h0 = FwdValidators s h1)"

text "Another type of sourcing allows changing the validator sets.
The forward validator set of the source needs to coincide with the
rear validator set of the newly prepared hash.  This can only happen
when the older hash has been committed by both validator sets."

definition validators_change :: "situation \<Rightarrow> hash \<Rightarrow> hash \<Rightarrow> bool"
where
"validators_change s ancient next =
   (FwdValidators s ancient = RearValidators s next)"

fun prev_next_with_chosen_validators :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"prev_next_with_chosen_validators s (h0, v0) (h1, v1) =
  (PrevHash s h1 = Some h0 \<and> v1 = v0 + 1 \<and>
   (validators_match s h0 h1 \<or> validators_change s h0 h1 \<and> committed_by_both s h0 v0))
  "

inductive ancestor_descendant_with_chosen_validators :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
  inheritance_self: "ancestor_descendant_with_chosen_validators s (h, v) (h, v)"
| inheritances_step: "ancestor_descendant_with_chosen_validators s (h0, v0) (h1, v1) \<Longrightarrow>
                  prev_next_with_chosen_validators s (h1, v1) (h2, v2) \<Longrightarrow>
                  ancestor_descendant_with_chosen_validators s (h0, v0) (h2, v2)"

text "Accountable safety will prevent forks (unless some number of validators are slashed).
The fork is defined using two branches whose tips do not belong to the same chain.
The branches are made of hashes with valid validator transitions (otherwise, sometimes,
we cannot blame any validators for the fork)."

fun fork :: "situation \<Rightarrow>
             (hash \<times> view) \<Rightarrow>
             (hash \<times> view) \<Rightarrow>
             (hash \<times> view) \<Rightarrow> bool"
where
"fork s (root, v) (h1, v1) (h2, v2) =
  (\<not> on_same_chain s h1 h2 \<and>
   ancestor_descendant_with_chosen_validators s (root, v) (h1, v1) \<and>
   ancestor_descendant_with_chosen_validators s (root, v) (h2, v2))"

text "A fork is particularly harmful when their tips and the root are all committed."

fun fork_with_commits :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"fork_with_commits s (h, v) (h1, v1) (h2, v2) =
   (fork s (h, v) (h1, v1) (h2, v2) \<and>
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"

subsection "Prepare Messages' Sources"

text "In the next section, we are going to determine which of the validators are slashed in a situation."

text "One slashing condition requires sources for prepare messages.  Here we define what constitutes
a source."

fun sourcing_normal :: "situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_normal s h (h', v', v_src) =
  (\<exists> v_ss.
   prepared_by_both s h v_src v_ss \<and>
   -1 \<le> v_ss \<and>
   v_ss < v_src \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_match s h h' )"

fun sourcing_switching_validators ::
"situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing_switching_validators s h (h', v', v_src) =
  (\<exists> v_ss.
   prepared_by_both s h v_src v_ss \<and>
   committed_by_both s h v_src \<and>
   -1 \<le> v_ss \<and>
   v_ss < v_src \<and>
   nth_ancestor s (nat (v' - v_src)) h' = Some h \<and>
   validators_change s h h')"

text "A prepare message's source needs to be one of these two types."

definition sourcing :: "situation \<Rightarrow> hash \<Rightarrow> (hash \<times> view \<times> view) \<Rightarrow> bool"
where
"sourcing s h_old tri = (sourcing_normal s h_old tri \<or> sourcing_switching_validators s h_old tri)"

subsection "Slashing Conditions"

text "In a situation, a validator might be slashed or not.  A validator is slashed individually
although later we will be often talking ``unless one-third of the validators are slashed.''
"

text "[i] A validator is slashed when it has sent a commit message of a hash
      that is not prepared yet."

definition slashed_one :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_one s n =
    (\<exists> h v.
      ((n, Commit (h, v)) \<in> Messages s \<and>
    (\<not> (\<exists> vs. -1 \<le> vs \<and> vs < v \<and> prepared_by_both s h v vs) )))"

text "[ii] A validator is slashed when it has sent a prepare message whose
      view src is not -1 but has no supporting preparation in the view src."

definition slashed_two :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_two s n =
  (\<exists> h v v_src.
       ((n, Prepare (h, v, v_src)) \<in> Messages s \<and>
       v_src \<noteq> -1 \<and>
       (\<not> (\<exists> h_anc. sourcing s h_anc (h, v, v_src)))))"

text "[iii] A validator is slashed when it has sent a commit message and a prepare message
     containing view numbers in a specific constellation."

definition slashed_three :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_three s n =
    (\<exists> x y v w u.
      (n, Commit (x, v)) \<in> Messages s \<and>
      (n, Prepare (y, w, u)) \<in> Messages s \<and>
      u < v \<and> v < w)"

text "[iv] A validator is slashed when it has signed two different Prepare messages at the same view."

definition slashed_four :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed_four s n =
    (\<exists> x1 x2 v vs1 vs2.
      (n, Prepare (x1, v, vs1)) \<in> Messages s \<and>
      (n, Prepare (x2, v, vs2)) \<in> Messages s \<and>
      (x1 \<noteq> x2 \<or> vs1 \<noteq> vs2))"


text "A validator is slashed when at least one of the above conditions [i]--[iv] hold."

definition slashed :: "situation \<Rightarrow> validator \<Rightarrow> bool"
where
"slashed s n = (slashed_one s n \<or>
                slashed_two s n \<or>
                slashed_three s n \<or>
                slashed_four s n)"

text "We will be frequently talking about one-third of some validators being slashed."

definition one_third_slashed :: "situation \<Rightarrow> validator set \<Rightarrow> bool"
where
"one_third_slashed s vs = one_third vs (slashed s)"

definition one_third_of_rear_slashed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"one_third_of_rear_slashed s h = one_third (RearValidators s h) (slashed s)"

definition one_third_of_fwd_slashed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"one_third_of_fwd_slashed s h = one_third (FwdValidators s h) (slashed s)"

text "In the end, accountable safety will slash at least one-third of fwd-or-rear validator sets."

definition one_third_of_fwd_or_rear_slashed :: "situation \<Rightarrow> hash \<Rightarrow> bool"
where
"one_third_of_fwd_or_rear_slashed s h = (one_third_of_fwd_slashed s h \<or> one_third_of_rear_slashed s h)"


section "Auxiliary Things (skippable)"

subsection "Validator History Tracking"

text "In the statement of accountable safety, we need to be a bit specific about
which validator set the slashed validators belong to.  A singleton is also a validator set
and the 2/3 of a random singleton being slashed should not be significant.
So, when we have a fork, we start from the root of the fork and identify the heirs of the initial
validator sets.  Our statement says 2/3 of a heir validator set are slashed.
"

text "There are two ways of inheriting the title of relevant validator set.
These correspond to the two ways of sourcing a prepare message."

fun inherit_normal :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"inherit_normal s (h_old, v_src) (h_new, v) =
   (prepared_by_both s h_new v v_src \<and> -1 \<le> v_src \<and> v_src < v \<and>  sourcing_normal s h_old (h_new, v, v_src))"

fun inherit_switching_validators ::
  "situation \<Rightarrow> (hash \<times> view) \<Rightarrow>
                (hash \<times> view) \<Rightarrow> bool"
where
"inherit_switching_validators s (h_old, v_old) (h_new, v_new) =
   (prepared_by_both s h_new v_new v_old \<and> -1 \<le> v_old \<and> v_old < v_new \<and>
    sourcing_switching_validators s h_old (h_new, v_new, v_old))"

text "The heir relation is just zero-or-more repetition of the inheritance."

inductive heir :: "situation \<Rightarrow>
                   (hash \<times> view) \<Rightarrow> 
                   (hash \<times> view) \<Rightarrow> bool"
where
  heir_self : "prepared_by_both s h v v_src \<Longrightarrow> heir s (h, v) (h, v)"
| heir_normal_step : "heir s (h, v) (h', v') \<Longrightarrow>
                 inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
                 ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
                 heir s (h, v) (h'', v'')"
| heir_switching_step : "heir s (h, v) (h', v') \<Longrightarrow>
                 inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
                 ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
                 heir s (h, v) (h'', v'')"

text "When two hashes are not in the inheritance relation in either direction,
the two hashes are not on the same heir chain.  In the statement of accountable safety,
we use this concept to detect conflicts (which should not happen until 2/3 of a legitimate
heir are slashed)."

definition on_same_heir_chain :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"on_same_heir_chain s x y = (heir s x y \<or> heir s y x)"

text "When heirs are not on the same chain of legitimacy, they have forked."

fun legitimacy_fork :: "situation \<Rightarrow>
                    (hash \<times> view) \<Rightarrow>
                    (hash \<times> view) \<Rightarrow>
                    (hash \<times> view) \<Rightarrow> bool"
where
"legitimacy_fork s (root, v) (h1, v1) (h2, v2) =
  (\<not> on_same_heir_chain s (h1, v1) (h2, v2) \<and> heir s (root, v) (h1, v1) \<and> heir s (root, v) (h2, v2))"

text "A fork is particularly bad when the end points are committed, not only prepared."

fun legitimacy_fork_with_commits :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"legitimacy_fork_with_commits s (h, v) (h1, v1) (h2, v2) =
   (legitimacy_fork s (h, v) (h1, v1) (h2, v2) \<and>
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"


subsection "Sets and Arithmetics"

lemma sum_suc_disj :
 "n_one + n_two \<le> Suc k \<Longrightarrow>
  n_one + n_two \<le> k \<or>
  n_one + n_two = Suc k"
using le_SucE by blast

lemma sum_eq_disj :
"((n_one :: nat) \<le> 1 \<and> (n_two :: nat) \<le> 1) \<or>
  n_one > 1 \<or> n_two > 1
"
by auto

lemma sum_eq_case1 :
  "n_one + n_two = Suc k \<Longrightarrow>
   n_one > 1 \<Longrightarrow>
   \<exists> n_one_pre. n_one_pre \<ge> 1 \<and> n_one = Suc n_one_pre \<and> n_one_pre + n_two = k"
using less_imp_Suc_add by fastforce

lemma sum_eq_case2 :
  "n_one + n_two = Suc k \<Longrightarrow>
   n_two > 1 \<Longrightarrow>
   \<exists> n_two_pre. n_two_pre \<ge> 1 \<and> n_two = Suc n_two_pre \<and> n_one + n_two_pre = k"
by presburger
 

lemma sum_suc :
 "n_one + n_two \<le> Suc k \<Longrightarrow>
  n_one + n_two \<le> k \<or>
  n_one \<le> 1 \<and> n_two \<le> 1 \<or>
  (\<exists> n_one_pre. n_one_pre \<ge> 1 \<and> n_one = Suc n_one_pre \<and> n_one_pre + n_two = k) \<or>
  (\<exists> n_two_pre. n_two_pre \<ge> 1 \<and> n_two = Suc n_two_pre \<and> n_one + n_two_pre = k)
 "
using sum_eq_case1 sum_eq_case2 by auto


lemma card_not [simp] :
  "finite s \<Longrightarrow>
   card {n \<in> s. \<not> f n} = card s - card {n \<in> s. f n}"
proof -
  assume "finite s"
  then have "card (s - {n \<in> s. f n}) = card s - card {n \<in> s. f n}"
    by (rule_tac Finite_Set.card_Diff_subset; auto)
  moreover have "{n \<in> s. \<not> f n} = s - {n \<in> s. f n}"
    by blast
  ultimately show ?thesis by auto
qed


lemma set_conj [simp] :
  "{n \<in> s. f n \<and> g n} = {n \<in> s. f n} \<inter> {n \<in> s. g n}"
by blast


lemma two_more_two_set :
  "finite s \<Longrightarrow>
    2 * card s \<le> 3 * card {n \<in> s. f n} \<Longrightarrow>
    2 * card s < 3 * card {n \<in> s. g n} \<Longrightarrow>
    card s
    < 3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
"
proof -
  assume "finite s"
  then have " card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
            = card {n \<in> s. f n} + card { n \<in> s. g n} - card ({n \<in> s. f n} \<union> {n \<in> s. g n})"
    proof -
      assume "finite s"
      then have "card {n \<in> s. f n} + card { n \<in> s. g n} = card ({n \<in> s. f n} \<union> {n \<in> s. g n}) + card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
        by (rule_tac Finite_Set.card_Un_Int; auto)
      then show ?thesis
        by auto
    qed
  moreover assume "finite s"
  then moreover have "card ({n \<in> s. f n} \<union> {n \<in> s. g n}) \<le> card s"
    by (rule Finite_Set.card_mono; auto)
  ultimately have "card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> card {n \<in> s. f n} + card { n \<in> s. g n} - card s"
    by auto
  then have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> 3 * card {n \<in> s. f n} + 3 * card { n \<in> s. g n} - 3 * card s"
    by auto
  moreover assume "2 * card s \<le> 3 * card {n \<in> s. f n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   \<ge> 3 * card { n \<in> s. g n} - card s"
    by auto
  moreover assume "2 * card s < 3 * card {n \<in> s. g n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   > card s"
    by auto
  then show ?thesis
    by auto
qed


lemma card_nonzero_exists :
"card {n \<in> s. f n} > 0 \<Longrightarrow>
 \<exists> n \<in> s. f n"
(* sledgehammer *)
	by (metis (no_types, lifting) Collect_empty_eq card_0_eq card_ge_0_finite not_gr_zero)


lemma card_conj_le :
  "finite s \<Longrightarrow>
     card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
   = card {n \<in> s. f n} + card { n \<in> s. g n} - card ({n \<in> s. f n} \<union> {n \<in> s. g n})"
proof -
 assume "finite s"
 then have "card {n \<in> s. f n} + card { n \<in> s. g n} = card ({n \<in> s. f n} \<union> {n \<in> s. g n}) + card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
   by (rule_tac Finite_Set.card_Un_Int; auto)
 then show ?thesis
   by auto
qed

lemma two_two_set :
 "2 * card s \<le> 3 * card {n \<in> s. f n} \<Longrightarrow>
  2 * card s \<le> 3 * card {n \<in> s. g n} \<Longrightarrow>
  finite s \<Longrightarrow>
  card s \<le> 3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
proof -
  assume "finite s"
  then have " card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
            = card {n \<in> s. f n} + card { n \<in> s. g n} - card ({n \<in> s. f n} \<union> {n \<in> s. g n})"
    proof -
      assume "finite s"
      then have "card {n \<in> s. f n} + card { n \<in> s. g n} = card ({n \<in> s. f n} \<union> {n \<in> s. g n}) + card ({n \<in> s. f n} \<inter> {n \<in> s. g n})"
        by (rule_tac Finite_Set.card_Un_Int; auto)
      then show ?thesis
        by auto
    qed
  moreover assume "finite s"
  then moreover have "card ({n \<in> s. f n} \<union> {n \<in> s. g n}) \<le> card s"
    by (rule Finite_Set.card_mono; auto)
  ultimately have "card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> card {n \<in> s. f n} + card { n \<in> s. g n} - card s"
    by auto
  then have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                 \<ge> 3 * card {n \<in> s. f n} + 3 * card { n \<in> s. g n} - 3 * card s"
    by auto
  moreover assume "2 * card s \<le> 3 * card {n \<in> s. f n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   \<ge> 3 * card { n \<in> s. g n} - card s"
    by auto
  moreover assume "2 * card s \<le> 3 * card {n \<in> s. g n}"
  ultimately have "3 * card ({n \<in> s. f n} \<inter> {n \<in> s. g n})
                   \<ge> card s"
    by auto
  then show ?thesis
    by auto
qed


lemma inclusion_card_le :
  "\<forall>n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n \<Longrightarrow>
   finite (Validators s) \<Longrightarrow>
   card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
proof -
  assume "\<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
  moreover assume "finite (Validators s)"
  ultimately show "card {n \<in> Validators s. f n} \<le> card {n \<in> Validators s. g n}"
    proof -
      assume "\<forall> n. n \<in> Validators s \<longrightarrow> f n \<longrightarrow> g n"
      then have "{n \<in> Validators s. f n} \<subseteq> {n \<in> Validators s. g n}"
        by blast
      moreover assume "finite (Validators s)"
      ultimately show ?thesis
        by (simp add: card_mono)
    qed
qed

lemma nat_min_min :
"    vs1 < v \<Longrightarrow>
    \<not> vs1 < c_view \<Longrightarrow>
   (nat (v - vs1) + nat (vs1 - c_view)) = nat (v - c_view)"
by (simp add: Nat_Transfer.transfer_nat_int_functions(1))

lemma view_total [simp]:
  "(v2 :: view) \<le> v1 \<or> v1 \<le> v2"
apply auto
done


lemma sum_is_suc_dest :
   "Suc n = n1 + n2 \<Longrightarrow>
    ((\<exists> n1'. n1 = Suc n1' \<and> n = n1' + n2) \<or>
     (\<exists> n2'. n2 = Suc n2' \<and> n = n1 + n2'))
   "
apply (case_tac n1; auto)
done

(* Finding a max element in a set of integers *)
lemma find_max_ind_step :
  "\<forall>u. n = nat (u - s) \<longrightarrow> s \<in> (S :: int set) \<longrightarrow> (\<forall>x. x \<in> S \<longrightarrow> x \<le> u)
                         \<longrightarrow> (\<exists>m. m \<in> S \<and> (\<forall>y>m. y \<notin> S)) \<Longrightarrow>
   Suc n = nat (u - s) \<Longrightarrow> s \<in> S \<Longrightarrow> \<forall>x. x \<in> S \<longrightarrow> x \<le> u \<Longrightarrow> \<exists>m. m \<in> S \<and> (\<forall>y>m. y \<notin> S)"
apply(case_tac "\<forall> x. x \<in> S \<longrightarrow> x \<le> u - 1")
 apply(drule_tac x = "u - 1" in spec)
 apply simp
by force


lemma find_max_ind :
  "\<forall> u.
   n = nat (u - s) \<longrightarrow>
   s \<in> (S :: int set) \<longrightarrow>
   (\<forall> x. x \<in> S \<longrightarrow> x \<le> u) \<longrightarrow>
   (\<exists> m. m \<in> S \<and>
      (\<forall> y. y > m \<longrightarrow> y \<notin> S))"
apply(induction n; auto)
 apply force
apply(rule_tac n = n and u = u and S = S and s = s in find_max_ind_step; auto)
done

lemma find_max :
  "s \<in> (S :: int set) \<Longrightarrow>
   \<forall> x. x \<in> S \<longrightarrow> x \<le> u \<Longrightarrow>
   \<exists> m. m \<in> S \<and>
      (\<forall> y. y > m \<longrightarrow> y \<notin> S)"
using find_max_ind by auto

lemma one_third_mp :
  "finite X \<Longrightarrow>
   \<forall> v. p v \<longrightarrow> q v \<Longrightarrow>
   one_third X p \<Longrightarrow> one_third X q"
apply(simp add: one_third_def)
 apply(subgoal_tac "card {n \<in> X. p n} \<le> card {n \<in> X. q n}")
 apply linarith
apply(subgoal_tac "finite {n \<in> X. q n}")
 apply(subgoal_tac "{n \<in> X. p n} \<subseteq> {n \<in> X. q n}")
  using card_mono apply blast
 apply blast
by simp

lemma two_thirds_two_thirds_one_third :
  "finite X \<Longrightarrow>
    two_thirds X p \<Longrightarrow>
    two_thirds X q \<Longrightarrow>
    one_third X (\<lambda> x. p x \<and> q x)
  "
apply(simp add: two_thirds_def one_third_def)
apply(rule_tac two_two_set)
  apply simp
 apply simp
apply simp
done

subsection "Validator History Tracking"

lemma ancestor_with_same_view :
 "ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
  snd (h, v) \<le> snd (h1, v1) \<and>
  (snd (h, v) = snd (h1, v1) \<longrightarrow> fst (h, v) = fst (h1, v1))"
apply(induction rule: ancestor_descendant_with_chosen_validators.induct)
 apply simp
apply auto
done

lemma heir_increases_view :
  "heir s t t' \<Longrightarrow> snd t \<le> snd t'"
apply(induction rule: heir.induct; auto)
done

inductive heir_after_n_switching ::
   "nat \<Rightarrow> situation \<Rightarrow>
    (hash \<times> view) \<Rightarrow>
    (hash \<times> view) \<Rightarrow> bool"
where
  heir_n_self : "prepared_by_both s h v v_src \<Longrightarrow> heir_after_n_switching 0 s (h, v) (h, v)"
| heir_n_normal_step :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
    inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
    heir_after_n_switching n s (h, v) (h'', v'')"
| heir_n_switching_step :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
    inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
    heir_after_n_switching (Suc n) s (h, v) (h'', v'')"



lemma every_heir_is_after_n_switching :
"heir s p0 p1 \<Longrightarrow> \<exists> n. heir_after_n_switching n s p0 p1"
apply(induction rule: heir.induct)
  apply(rule_tac x = 0 in exI)
  apply (simp add: heir_n_self)
 apply clarify
 apply(rule_tac x = n in exI)
 apply(rule heir_n_normal_step; blast)
apply clarify
using heir_n_switching_step by blast


fun legitimacy_fork_with_n_switching :: "situation \<Rightarrow>
             (hash \<times> view) \<Rightarrow>
             nat \<Rightarrow> (hash \<times> view) \<Rightarrow>
             nat \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"legitimacy_fork_with_n_switching
   s (root, v) n1 (h1, v1) n2 (h2, v2) =
   (\<not> on_same_heir_chain s (h1, v1) (h2, v2) \<and>
    heir_after_n_switching n1 s (root, v) (h1, v1) \<and>
    heir_after_n_switching n2 s (root, v) (h2, v2))"

lemma legitimacy_fork_has_n_switching :
  "legitimacy_fork s (r, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> n1 n2. legitimacy_fork_with_n_switching s (r, v) n1 (h1, v1) n2 (h2, v2)"
apply(simp)
using every_heir_is_after_n_switching by blast

lemma ancestor_descendant_with_chosen_validators_trans:
  "ancestor_descendant_with_chosen_validators s (h1, v1) (h2, v2) \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h0, v0) (h1, v1) \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h0, v0) (h2, v2)"
apply(induction rule: ancestor_descendant_with_chosen_validators.induct)
 apply blast
using inheritances_step by blast


lemma heir_decomposition :
  "heir s (h, v) (h'', v'') \<Longrightarrow>
    ((\<exists> v_src. h = h'' \<and> v = v'' \<and> prepared_by_both s h v v_src) \<or>
     (\<exists> h' v'. heir s (h, v) (h', v') \<and> inherit_normal s (h', v') (h'', v'')) \<or>
     (\<exists> h' v'. heir s (h, v) (h', v') \<and> inherit_switching_validators s (h', v') (h'', v''))
    )"
apply(erule_tac DynamicValidatorSetOneMessage.heir.cases)
  apply(rule disjI1)
  apply blast
 apply(rule disjI2)
 apply(rule disjI1)
 apply blast
apply(rule disjI2)
apply(rule disjI2)
by blast


lemma heir_same_height :
 "heir s (h', v) (h, v) \<Longrightarrow>
  h' = h"
apply(drule heir_decomposition)
using heir_increases_view by fastforce


fun legitimacy_fork_with_center :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"legitimacy_fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) =
   (legitimacy_fork s (h, v) (h1, v1) (h2, v2) \<and>
    heir s (h_orig, v_orig) (h, v) \<and> (* This is used to connect the whole setup with the original statement *)
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"

fun legitimacy_fork_with_center_with_n_switching :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow>
      (hash \<times> view) \<Rightarrow> nat \<Rightarrow> (hash \<times> view) \<Rightarrow> nat \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"legitimacy_fork_with_center_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2) =
   (legitimacy_fork_with_n_switching s (h, v) n1 (h1, v1) n2 (h2, v2) \<and>
    heir s (h_orig, v_orig) (h, v) \<and> (* This is used to connect the whole setup with the original statement *)
    committed_by_both s h v \<and>
    committed_by_both s h1 v1 \<and>
    committed_by_both s h2 v2)"

lemma legitimacy_fork_with_center_has_n_switching :
  "legitimacy_fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> n1 n2.
    legitimacy_fork_with_center_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2)"
apply simp
using every_heir_is_after_n_switching by blast

fun legitimacy_fork_root_views :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> view set"
where
"legitimacy_fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2) =
  { v. (\<exists> h. legitimacy_fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2)) }"

(* It's convenient to have a fork's root as the latest commit immediately before the fork.
 * Otherwise the induction has hairier case analysis.
 *)
fun legitimacy_fork_with_center_with_high_root ::
  "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
  "legitimacy_fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) =
     (legitimacy_fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<and>
      (\<forall> h' v'. v' > v \<longrightarrow>
        \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h1, v1) (h2, v2)))"

fun legitimacy_fork_with_center_with_high_root_with_n_switching ::
  "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> nat \<Rightarrow> (hash \<times> view) \<Rightarrow>
                nat \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
  "legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2) =
     (legitimacy_fork_with_center_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2) \<and>
      (\<forall> h' v'. v' > v \<longrightarrow>
        \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h1, v1) (h2, v2)))"

lemma legitimacy_fork_with_center_with_high_root_has_n_switching :
  "legitimacy_fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> n1 n2.
     legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n1 (h1, v1) n2 (h2, v2)"
apply simp
using every_heir_is_after_n_switching by blast

lemma legitimacy_fork_with_center_choose_high_root :
  "legitimacy_fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
   \<exists> h' v'. legitimacy_fork_with_center_with_high_root s (h_orig, v_orig) (h', v') (h1, v1) (h2, v2)"
proof -
 assume "legitimacy_fork_with_center s (h_orig, v_orig) (h, v) (h1, v1) (h2, v2)"
 then have "v \<in> legitimacy_fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2)"
   by auto
 moreover have "\<forall> x. x \<in> legitimacy_fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2) \<longrightarrow> x \<le> v1"
   using heir_increases_view by auto
 ultimately have "\<exists> m. m \<in> legitimacy_fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2) \<and>
                   (\<forall> y. y > m \<longrightarrow> y \<notin> legitimacy_fork_root_views s (h_orig, v_orig) (h1, v1) (h2, v2))"
   by(rule_tac find_max; auto)
 then show ?thesis
   by (clarsimp; blast)
qed

lemma forget_number_of_switching:
 "heir_after_n_switching n s (h_twoa, v_twoa) (h_one, v_one)
  \<Longrightarrow> heir s (h_twoa, v_twoa) (h_one, v_one)"
apply(induction rule: heir_after_n_switching.induct)
  apply (simp add: heir_self)
 using heir_normal_step apply blast
using heir_switching_step by blast


lemma inherit_normal_means_heir :
  "inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
   heir s (h', v') (h'', v'')"
by (meson heir_normal_step heir_self inherit_normal.simps sourcing_normal.simps)


lemma chain_and_inherit :
   "inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
    v_two \<le> snd (h'', v'') \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
    v_two \<le> snd (h', v') \<Longrightarrow>
    on_same_heir_chain s (h', v') (h_two, v_two) \<Longrightarrow> False"
apply(subgoal_tac "heir s (h', v') (h'', v'')")
 apply(simp only: on_same_heir_chain_def)
 apply(erule disjE)
  using heir_increases_view heir_same_height apply fastforce
 using heir_normal_step apply blast
using inherit_normal_means_heir by blast

lemma one_validator_change_leaves_one_set :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n = 0 \<and> FwdValidators s (fst (h, v)) = FwdValidators s (fst (h', v')) \<or>
    n = 1 \<and> FwdValidators s (fst (h, v)) = RearValidators s (fst (h', v'))"
apply(induction rule: heir_after_n_switching.induct)
  apply blast
 apply (simp add: validators_match_def)
 apply blast
apply(subgoal_tac "n = 0")
 defer
 apply linarith
by (metis (no_types, lifting) One_nat_def fstI inherit_switching_validators.elims(2) sourcing_switching_validators.simps validators_change_def zero_le_one zero_neq_one)


lemma prepared_by_fwd_of_origin :
"   n \<le> Suc 0 \<Longrightarrow>
    heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
    prepared s (FwdValidators s h) h'' v'' v'
"
apply(simp only: inherit_normal.simps prepared_by_both_def prepared_by_fwd_def prepared_by_rear_def)
apply(subgoal_tac " (FwdValidators s h) = (FwdValidators s h'') \<or>
                    (FwdValidators s h) = (RearValidators s h'')")
 apply auto[1]
by (metis fst_conv one_validator_change_leaves_one_set sourcing_normal.simps validators_match_def)

lemma heir_found_switching :
  "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
   inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
   0 < Suc n \<Longrightarrow>
   \<exists>h_one v_one h_two v_two.
      heir_after_n_switching (Suc n - 1) s (h, v) (h_one, v_one) \<and>
      inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
      heir_after_n_switching 0 s (h_two, v_two) (h'', v'')"
apply(rule_tac x = h' in exI)
apply(rule_tac x = v' in exI)
apply(rule_tac x = h'' in exI)
apply(rule_tac x = v'' in exI)
apply simp
using heir_n_self by blast

lemma heir_trans :
  "heir s (h_r, v_r) (h', v') \<Longrightarrow>
   heir s (h, v) (h_r, v_r) \<Longrightarrow>
   heir s (h, v) (h', v')"
apply(induction rule: heir.induct; auto)
 apply(rule_tac h' = h' and v' = v' in heir_normal_step; auto)
apply(rule_tac h' = h' and v' = v' in heir_switching_step; auto)
done

lemma heir_normal_extend :
      "(\<exists>h_one v_one h_two v_two.
           heir_after_n_switching n s (h, v) (h_one, v_one) \<and>
           inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
           heir_after_n_switching 0 s (h_two, v_two) (h', v')) \<Longrightarrow>
       ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
       inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
       (\<exists>h_one v_one h_two v_two.
           heir_after_n_switching n s (h, v) (h_one, v_one) \<and>
           inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
           heir_after_n_switching 0 s (h_two, v_two) (h'', v''))"
apply clarify
apply(rule_tac x = h_one in exI)
apply(rule_tac x = v_one in exI)
apply(rule_tac x = h_two in exI)
apply(rule_tac x = v_two in exI)
apply simp
using heir_n_normal_step inherit_normal.simps sourcing_normal.simps by blast

lemma heir_after_one_or_more_switching_dest :
  "heir_after_n_switching na s (h, v) (h_three, v_three) \<Longrightarrow>
   na > 0 \<Longrightarrow>
   (\<exists> h_one v_one h_two v_two.
    heir_after_n_switching (na - 1) s (h, v) (h_one, v_one) \<and>
    ancestor_descendant_with_chosen_validators s (h_one, v_one) (h_two, v_two) \<and>
    inherit_switching_validators s (h_one, v_one) (h_two, v_two) \<and>
    heir_after_n_switching 0 s (h_two, v_two) (h_three, v_three))"
apply(induction rule: heir_after_n_switching.induct)
  apply simp
 using heir_n_normal_step apply blast
by (metis diff_Suc_1 heir_n_self inherit_switching_validators.simps)

lemma high_point_still_high :
(* remove unnecessary assumptions *)
      "1 \<le> n_one_pre \<Longrightarrow>
       \<forall>h' v'. v < v' \<longrightarrow> \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
       \<not> on_same_heir_chain s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
       heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
       heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
       committed_by_both s h v \<Longrightarrow>
       committed_by_both s h_one v_one \<Longrightarrow>
       committed_by_both s h_two v_two \<Longrightarrow>
       heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
       inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
       ancestor_descendant_with_chosen_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
       heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
       \<forall>h' v'. v < v' \<longrightarrow> \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h_onea, v_onea) (h_two, v_two)"
apply(rule allI)
apply(rule allI)
apply(drule_tac x = h' in spec)
apply(drule_tac x = v' in spec)
apply(rule impI)
by (metis forget_number_of_switching legitimacy_fork.simps legitimacy_fork_with_center.simps heir_switching_step heir_trans)

lemma at_least_one_switching_means_higher :
  "heir_after_n_switching n_one_pre s (h, v) (h_onea, v_onea) \<Longrightarrow>
   Suc 0 \<le> n_one_pre \<Longrightarrow>
   snd (h, v) < snd (h_onea, v_onea)"
apply(induction rule: heir_after_n_switching.induct; auto)
using forget_number_of_switching heir_increases_view by fastforce

lemma shallower_legitimacy_fork :
   "heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_one v_one \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_two, v_two) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir s (h_onea, v_onea) (h_two, v_two) \<Longrightarrow> (* how to get this? *)
    v < v_onea \<Longrightarrow> legitimacy_fork_with_center s (h_orig, v_orig) (h_onea, v_onea) (h_one, v_one) (h_two, v_two)"
apply(simp only: legitimacy_fork_with_center.simps)
apply(rule conjI)
 apply(simp only:legitimacy_fork.simps)
  apply (meson forget_number_of_switching heir_self heir_switching_step heir_trans inherit_switching_validators.simps on_same_heir_chain_def sourcing_switching_validators.simps)
by (meson forget_number_of_switching heir_trans inherit_switching_validators.simps sourcing_switching_validators.simps)

lemma on_same_heir_chain_sym :
 "on_same_heir_chain s (h_one, v_one) (h_two, v_two) =
  on_same_heir_chain s (h_two, v_two) (h_one, v_one)"
	using on_same_heir_chain_def by auto

lemma legitimacy_fork_with_center_with_high_root_with_n_switching_sym :
   "legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one)
     n_two (h_two, v_two) \<Longrightarrow>
    legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_two (h_two, v_two)
     n_one (h_one, v_one)"
apply auto
using on_same_heir_chain_sym by blast

subsection "Slashing Related"

lemma slashed_four_means_slashed_on_a_group:
   "finite X \<Longrightarrow> one_third X (slashed_four s) \<Longrightarrow> one_third X (slashed s)"
using one_third_mp slashed_def by blast

lemma slashed_four_on_a_group:
  " finite (FwdValidators s h) \<Longrightarrow>
    prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow>
    \<exists>v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src \<Longrightarrow> h'' \<noteq> h_two \<Longrightarrow>
    one_third (FwdValidators s h) (slashed_four s)"
apply(simp only: prepared_def two_thirds_sent_message_def)
apply(erule exE)
apply(subgoal_tac
       "one_third (FwdValidators s h)
           (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and>
                (n, Prepare (h_two, v'', v_two_src)) \<in> Messages s)
       ")
 apply(subgoal_tac "\<forall> n. 
               ((n, Prepare (h'', v'', v')) \<in> Messages s \<and>
                (n, Prepare (h_two, v'', v_two_src)) \<in> Messages s) \<longrightarrow>
               slashed_four s n")
  apply (simp add: one_third_mp)
 using slashed_four_def apply blast
by (simp add: two_thirds_two_thirds_one_third)

lemma committed_so_prepared :
  " finite (FwdValidators s h) \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v'') \<Longrightarrow>
    committed_by_both s h_two v'' \<Longrightarrow>
    \<not> one_third (FwdValidators s h) (slashed s) \<Longrightarrow> prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow> \<exists>v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src"
apply(subgoal_tac "committed s (FwdValidators s h) h_two v''")
 apply (metis eq_fst_iff forget_number_of_switching heir_decomposition inherit_normal.simps inherit_switching_validators.simps one_validator_change_leaves_one_set prepared_by_both_def prepared_by_fwd_def prepared_by_rear_def)
using committed_by_both_def committed_by_fwd_def committed_by_rear_def one_validator_change_leaves_one_set by fastforce



lemma slashed_three_on_a_group :
 "finite X \<Longrightarrow>
  one_third X (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and> (n, Commit (h_two, v_two)) \<in> Messages s) \<Longrightarrow>
  v' < v_two \<Longrightarrow> v_two < v'' \<Longrightarrow> one_third X (slashed_three s)"
apply(rule one_third_mp; auto simp add: slashed_three_def)
apply blast
done

lemma slashed_three_on_group:
  " finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    one_third (FwdValidators s h) (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and> (n, Commit (h_two, v_two)) \<in> Messages s) \<Longrightarrow>
    v' < v_two \<Longrightarrow>
    v_two < v'' \<Longrightarrow>
    one_third (FwdValidators s h) (slashed_three s)"
proof -
  assume a1: "v' < v_two"
  assume a2: "v_two < v''"
  assume a3: "one_third (FwdValidators s h) (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and> (n, Commit (h_two, v_two)) \<in> Messages s)"
  assume a4: "finite (FwdValidators s (fst (h, v)))"
  have f5: "\<not> 0 \<le> v' + - 1 * v_two"
    using a1 by force
  have f6: "\<not> v'' + - 1 * v_two \<le> 0"
    using a2 by auto
  have f7: "\<forall>V p pa. (infinite V \<or> (\<exists>v. p v \<and> \<not> pa v) \<or> \<not> one_third V p) \<or> one_third V pa"
    by (meson one_third_mp)
  obtain vv :: "(validator \<Rightarrow> bool) \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> validator" where
    "\<forall>x0 x1. (\<exists>v3. x1 v3 \<and> \<not> x0 v3) = (x1 (vv x0 x1) \<and> \<not> x0 (vv x0 x1))"
    by moura
  then have f8: "\<forall>V p pa. (infinite V \<or> p (vv pa p) \<and> \<not> pa (vv pa p) \<or> \<not> one_third V p) \<or> one_third V pa"
    using f7 by presburger
  have f9: "\<forall>x1 x2. ((x2::int) < x1) = (\<not> x1 + - 1 * x2 \<le> 0)"
    by auto
  have "\<forall>x0 x2. ((x0::int) < x2) = (\<not> 0 \<le> x0 + - 1 * x2)"
    by linarith
  then have "\<not> ((vv (slashed_three s) (\<lambda>v. (v, Prepare (h'', v'', v')) \<in> Messages s \<and> (v, Commit (h_two, v_two)) \<in> Messages s), Prepare (h'', v'', v')) \<in> Messages s \<and> (vv (slashed_three s) (\<lambda>v. (v, Prepare (h'', v'', v')) \<in> Messages s \<and> (v, Commit (h_two, v_two)) \<in> Messages s), Commit (h_two, v_two)) \<in> Messages s) \<or> slashed_three s (vv (slashed_three s) (\<lambda>v. (v, Prepare (h'', v'', v')) \<in> Messages s \<and> (v, Commit (h_two, v_two)) \<in> Messages s))"
    using f9 f6 f5 slashed_three_def by blast
  then show ?thesis
  using f8 a4 a3 by fastforce
qed

lemma smaller_induction_same_height_violation :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    finite (FwdValidators s h) \<Longrightarrow>
    prepared_by_both s h'' v'' v' \<and>
    (\<exists>v_ss. prepared_by_both s h' v' v_ss) \<and> - 1 \<le> v' \<and> v' < v'' \<and> nth_ancestor s (nat (v'' - v')) h'' = Some h' \<and> validators_match s h' h'' \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v'') \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v'') \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_two v'' \<Longrightarrow> \<not> one_third (FwdValidators s h) (slashed s) \<Longrightarrow> 
    prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow>  False"
apply(subgoal_tac "\<exists> v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src")
 apply(subgoal_tac "h'' \<noteq> h_two")
  apply(subgoal_tac "one_third (FwdValidators s h) (slashed_four s)")
   using slashed_four_means_slashed_on_a_group apply blast
  using slashed_four_on_a_group apply blast
 using heir_self on_same_heir_chain_def apply blast
using committed_so_prepared by blast

lemma smaller_induction_skipping_violation :
   "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    finite (FwdValidators s h) \<Longrightarrow>
    prepared_by_both s h'' v'' v' \<and> (\<exists>v_ss. prepared_by_both s h' v' v_ss) \<and> - 1 \<le> v' \<and> nth_ancestor s (nat (v'' - v')) h'' = Some h' \<and> validators_match s h' h'' \<Longrightarrow>
    v_two \<le> v'' \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    \<not> one_third (FwdValidators s h) (slashed s) \<Longrightarrow> \<not> v_two \<le> v' \<Longrightarrow> prepared s (FwdValidators s h) h'' v'' v' \<Longrightarrow>
    v_two \<noteq> v'' \<Longrightarrow> False"
apply(subgoal_tac "one_third (FwdValidators s h) (slashed_three s)")
 using one_third_mp slashed_def apply blast
apply(subgoal_tac "committed s (FwdValidators s h) h_two v_two")
 apply(simp add: prepared_def committed_def two_thirds_sent_message_def)
 apply(subgoal_tac "one_third (FwdValidators s h)
         (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and>
               (n, Commit (h_two, v_two)) \<in> Messages s)")
  apply(subgoal_tac "v_two > v'")
   apply(subgoal_tac "v_two < v''")
    using slashed_three_on_a_group apply blast
   apply linarith
  apply linarith
 apply(rule two_thirds_two_thirds_one_third; simp)
by (metis committed_by_both_def committed_by_fwd_def committed_by_rear_def fst_conv one_validator_change_leaves_one_set)

lemma smaller_induction_case_normal:
  "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
   (finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h', v') \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h', v') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False) \<Longrightarrow>
   inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
   finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
   v_two \<le> snd (h'', v'') \<Longrightarrow>
   n \<le> Suc 0 \<Longrightarrow>
   n_two \<le> Suc 0 \<Longrightarrow>
   \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
   heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
   committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False"
apply(case_tac "v_two \<le> snd (h', v')")
 apply(case_tac "on_same_heir_chain s (h', v') (h_two, v_two)")
	using chain_and_inherit apply blast
 apply blast
(* The group in question has prepared at v'' *)
apply(subgoal_tac "prepared s (FwdValidators s h) h'' v'' v'")
 defer
 using prepared_by_fwd_of_origin apply blast
apply(case_tac "v_two = v''")
 apply simp
 using smaller_induction_same_height_violation apply blast
apply simp
using smaller_induction_skipping_violation by blast

lemma some_h :
    "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
    inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
    heir s (h', v') (h'', v'')"
apply(subgoal_tac "\<exists> x. prepared_by_both s h' v' x")
 using heir_self heir_switching_step apply blast
by auto


lemma smaller_induction_switching_case:
  "heir_after_n_switching n s (h, v) (h', v') \<Longrightarrow>
   (finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h', v') \<Longrightarrow>
    n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h', v') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False) \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h', v') (h'', v'') \<Longrightarrow>
    inherit_switching_validators s (h', v') (h'', v'') \<Longrightarrow>
    finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h'', v'') \<Longrightarrow>
    Suc n \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h'', v'') (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) \<Longrightarrow> committed_by_both s h_two v_two \<Longrightarrow> \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False"
apply(case_tac "v_two < v'")
 apply(case_tac "\<not> on_same_heir_chain s (h', v') (h_two, v_two)")
  apply simp
 apply(subgoal_tac "heir s (h', v') (h_two, v_two)")
  using heir_increases_view apply force
 using heir_switching_step on_same_heir_chain_def apply blast
apply(case_tac "v' = v_two")
 apply(subgoal_tac "heir s (h', v') (h'', v'')")
  apply simp
  apply(subgoal_tac "\<exists> v'_src. prepared s (FwdValidators s h) h' v_two v'_src")
   apply(subgoal_tac "\<exists> v_two_src. prepared s (FwdValidators s h) h_two v_two v_two_src")
    apply(subgoal_tac "h' \<noteq> h_two")
     apply (meson slashed_four_means_slashed_on_a_group slashed_four_on_a_group)
    using on_same_heir_chain_def apply blast
   using committed_so_prepared apply blast
  using heir_same_height on_same_heir_chain_def apply blast
 using some_h apply blast
apply(subgoal_tac "v' < v_two")
 apply(subgoal_tac "prepared s (FwdValidators s h) h'' v'' v'")
  apply(subgoal_tac "committed s (FwdValidators s h) h_two v_two")
   apply(case_tac "v_two < v''")
    apply(subgoal_tac "one_third (FwdValidators s h)
         (\<lambda>n. (n, Prepare (h'', v'', v')) \<in> Messages s \<and>
              (n, Commit (h_two, v_two)) \<in> Messages s)")
     apply(subgoal_tac "one_third (FwdValidators s h) (slashed_three s)")
      apply (metis fst_conv one_third_mp slashed_def)
     apply(rule slashed_three_on_group)
        apply simp
       apply simp
      apply simp
     apply simp
    apply(simp only: prepared_def committed_def two_thirds_sent_message_def)
    apply(rule two_thirds_two_thirds_one_third; simp)
   apply simp
   apply(subgoal_tac "\<exists> v_two_src. prepared s (FwdValidators s h) h_two v'' v_two_src")
    apply(subgoal_tac "h'' \<noteq> h_two")
     apply (simp add: slashed_four_means_slashed_on_a_group slashed_four_on_a_group)
    using heir_self on_same_heir_chain_def apply blast
   using committed_so_prepared apply blast
  apply (metis committed_by_both_def committed_by_fwd_def committed_by_rear_def fst_conv one_validator_change_leaves_one_set)
 apply simp
 apply (metis One_nat_def Suc_neq_Zero fst_conv le_numeral_extra(1) one_validator_change_leaves_one_set prepared_by_both_def prepared_by_rear_def validators_change_def)
apply linarith
done


lemma accountable_safety_smaller_induction:
   "heir_after_n_switching n_one s (h, v) (h_one, v_one) \<Longrightarrow>
    finite (FwdValidators s (fst (h, v))) \<Longrightarrow>
    v_two \<le> snd (h_one, v_one) \<Longrightarrow>
    n_one \<le> Suc 0 \<Longrightarrow>
    n_two \<le> Suc 0 \<Longrightarrow>
    \<not> on_same_heir_chain s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s (fst (h, v)) (snd (h, v)) (* maybe not necessary *) \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    \<not> one_third (FwdValidators s (fst (h, v))) (slashed s) \<Longrightarrow> False"
apply(induction rule: heir_after_n_switching.induct)
  apply (simp add: forget_number_of_switching on_same_heir_chain_def)
 using smaller_induction_case_normal apply blast
using smaller_induction_switching_case by blast

lemma accountable_safety_from_legitimacy_fork_with_high_root_base_one_longer :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 v_one \<ge> v_two \<Longrightarrow>
 finite (FwdValidators s h) \<Longrightarrow>
 legitimacy_fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
apply(simp only: legitimacy_fork_with_center_with_high_root_with_n_switching.simps)
apply(simp only: legitimacy_fork_with_center_with_n_switching.simps)
apply(simp only: legitimacy_fork_with_n_switching.simps)
apply clarify
apply(rule_tac x = h in exI)
apply(rule_tac x = v in exI)
apply(rule conjI)
 apply simp
apply(case_tac "one_third_of_fwd_slashed s h")
 apply simp
apply(simp add: one_third_of_fwd_slashed_def)
using accountable_safety_smaller_induction by fastforce

lemma accountable_safety_from_legitimacy_fork_with_high_root_base_two_longer :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 v_one \<le> v_two \<Longrightarrow>
 finite (FwdValidators s h) \<Longrightarrow>
 legitimacy_fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
apply(rule_tac
      n_one = n_two
      and n_two = n_one
      and v_one = v_two
      and v_two = v_one
      and h_two = h_one
      and h_one = h_two
      and h = h and v = v
      in
      accountable_safety_from_legitimacy_fork_with_high_root_base_one_longer)
  apply blast
 apply simp
using on_same_heir_chain_def by auto

lemma accountable_safety_from_legitimacy_fork_with_high_root_base :
"n_one \<le> 1 \<and>
 n_two \<le> 1 \<and>
 legitimacy_fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 finite (FwdValidators s h) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
(* the forward set of h should have one-third slashed here. *)
(* Take the longer chain and do an induction
   and so, (prepared_view, prepared) and (committed, committed_view) is not in the relation
   make prepared shorter and shorter...!
 *)
apply(subgoal_tac "v_one \<le> v_two \<or> v_two \<le> v_one")
 apply (meson accountable_safety_from_legitimacy_fork_with_high_root_base_one_longer accountable_safety_from_legitimacy_fork_with_high_root_base_two_longer)
by linarith


subsection "Mainline Arguments for Accountable Safety"

lemma use_highness :
 "1 \<le> n_one_pre \<Longrightarrow>
    \<forall>h' v'. v < v' \<longrightarrow> \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_one v_one \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
    inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_two, v_two) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_one, v_one) (h_two, v_two) \<Longrightarrow> heir s (h_onea, v_onea) (h_two, v_two) \<Longrightarrow> False"
apply(drule_tac x = h_onea in spec)
apply(drule_tac x = v_onea in spec)
apply(subgoal_tac "v < v_onea")
 defer
 apply (metis One_nat_def at_least_one_switching_means_higher diff_Suc_1 snd_conv)
apply(subgoal_tac "legitimacy_fork_with_center s (h_orig, v_orig) (h_onea, v_onea) (h_one, v_one) (h_two, v_two)")
 apply blast
using shallower_legitimacy_fork by blast

lemma confluence_should_not:
  "1 \<le> n_one_pre \<Longrightarrow>
    \<forall>h' v'. v < v' \<longrightarrow> \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
    heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
    heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    committed_by_both s h_one v_one \<Longrightarrow>
    committed_by_both s h_two v_two \<Longrightarrow>
    heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
    heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_two, v_two) (h_one, v_one) \<Longrightarrow>
    \<not> heir s (h_one, v_one) (h_two, v_two) \<Longrightarrow> heir s (h_two, v_two) (h_onea, v_onea) \<Longrightarrow> False"
proof -
  assume "inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa)"
  moreover assume "ancestor_descendant_with_chosen_validators s (h_onea, v_onea) (h_twoa, v_twoa)"
  ultimately have "heir s (h_onea, v_onea) (h_twoa, v_twoa)"
    by (meson heir_self heir_switching_step inherit_switching_validators.simps sourcing_switching_validators.simps)
  moreover assume "heir s (h_two, v_two) (h_onea, v_onea)"
  ultimately have "heir s (h_two, v_two) (h_twoa, v_twoa)"
    using heir_trans by blast
  moreover assume "heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one)"
  then have "heir s (h_twoa, v_twoa) (h_one, v_one)"
    using forget_number_of_switching by blast
  ultimately have "heir s (h_two, v_two) (h_one, v_one)"
    using heir_trans by blast
  moreover assume " \<not> heir s (h_two, v_two) (h_one, v_one)"
  ultimately show "False"
    by blast
qed

lemma prev_switch_not_on_same_heir_chain :
"1 \<le> n_one_pre \<Longrightarrow>
\<forall>h' v'. v < v' \<longrightarrow> \<not> legitimacy_fork_with_center s (h_orig, v_orig) (h', v') (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 \<not> on_same_heir_chain s (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 heir s (h_orig, v_orig) (h, v) \<Longrightarrow>
 heir_after_n_switching n_two s (h, v) (h_two, v_two) \<Longrightarrow>
 committed_by_both s h v \<Longrightarrow>
 committed_by_both s h_one v_one \<Longrightarrow>
 committed_by_both s h_two v_two \<Longrightarrow>
 heir_after_n_switching (Suc n_one_pre - 1) s (h, v) (h_onea, v_onea) \<Longrightarrow>
 inherit_switching_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
 ancestor_descendant_with_chosen_validators s (h_onea, v_onea) (h_twoa, v_twoa) \<Longrightarrow>
 heir_after_n_switching 0 s (h_twoa, v_twoa) (h_one, v_one) \<Longrightarrow>
 \<not> on_same_heir_chain s (h_onea, v_onea) (h_two, v_two)"
apply(auto simp only: on_same_heir_chain_def)
  using use_highness apply blast
using confluence_should_not by blast

lemma reduce_legitimacy_fork :
   "legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) (Suc n_one_pre) (h_one, v_one)
     n_two (h_two, v_two) \<Longrightarrow>
    1 \<le> n_one_pre \<Longrightarrow>
    \<exists>h_one' v_one'.
       legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one_pre (h_one', v_one')
        n_two (h_two, v_two)"
apply (simp only: legitimacy_fork_with_center_with_high_root_with_n_switching.simps)
apply (simp only: legitimacy_fork_with_center_with_n_switching.simps)
apply (simp only: legitimacy_fork_with_n_switching.simps)
apply clarify
apply(drule
 heir_after_one_or_more_switching_dest)
 apply simp
apply clarify
apply(rule_tac x = "h_onea" in exI)
apply(rule_tac x = "v_onea" in exI)
apply(rule conjI)
 apply(rule conjI)
  apply(rule conjI)
   using prev_switch_not_on_same_heir_chain apply blast
  apply auto[1]
 apply auto[1]
using high_point_still_high by blast

lemma switching_induction_case_one :
  "\<forall>n_one n_twoa h_one v_one h_two v_two.
    n_one + n_twoa \<le> n_one_pre + n_two \<longrightarrow>
    finite (FwdValidators s h) \<longrightarrow>
    legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_twoa
     (h_two, v_two) \<longrightarrow>
     (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h') \<Longrightarrow>
    finite (FwdValidators s h) \<Longrightarrow>
    legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) (Suc n_one_pre) (h_one, v_one)
    n_two (h_two, v_two) \<Longrightarrow>
    1 \<le> n_one_pre \<Longrightarrow>
    k = n_one_pre + n_two \<Longrightarrow>
    \<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h'"
apply (subgoal_tac
"\<exists> h_one' v_one'.
 legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one_pre (h_one', v_one')
  n_two (h_two, v_two)")
 apply blast
using reduce_legitimacy_fork by blast

lemma some_symmetry :
  "\<forall>n_onea n_two h_one v_one h_two v_two.
       n_onea + n_two \<le> n_one + n_two_pre \<longrightarrow>
       finite (FwdValidators s h) \<longrightarrow>
       legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_two
        (h_two, v_two) \<longrightarrow>
       (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h') \<Longrightarrow>
    \<forall>n_onea n_twoa h_one v_one h_two v_two.
       n_onea + n_twoa \<le> n_two_pre + n_one \<longrightarrow>
       finite (FwdValidators s h) \<longrightarrow>
       legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_twoa
        (h_two, v_two) \<longrightarrow>
       (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h')"
apply clarify
apply (drule_tac x = n_onea in spec)
apply (drule_tac x = n_twoa in spec)
apply(drule_tac x = h_one in spec)
apply(drule_tac x = v_one in spec)
apply(drule_tac x = h_two in spec)
apply(drule_tac x = v_two in spec)
apply(erule impE)
 apply auto[1]
apply(erule impE)
 apply simp
apply(erule impE)
 apply blast
apply blast
done


lemma switching_induction_case_two :
"       \<forall>n_onea n_two h_one v_one h_two v_two.
          n_onea + n_two \<le> n_one + n_two_pre \<longrightarrow>
          finite (FwdValidators s h) \<longrightarrow>
          legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_onea (h_one, v_one) n_two
           (h_two, v_two) \<longrightarrow>
          (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h') \<Longrightarrow>
       finite (FwdValidators s h) \<Longrightarrow>
       legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one)
        (Suc n_two_pre) (h_two, v_two) \<Longrightarrow>
       1 \<le> n_two_pre \<Longrightarrow>
       k = n_one + n_two_pre \<Longrightarrow>
       \<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h'"
apply(rule_tac k = k and n_two = n_one and n_one_pre = n_two_pre and h = h and v = v
      and h_one = h_two and v_one = v_two and h_two = h_one and v_two = v_one
 in switching_induction_case_one)
 defer
 apply simp
 using legitimacy_fork_with_center_with_high_root_with_n_switching_sym apply blast
 using legitimacy_fork_with_center_with_high_root_with_n_switching_sym apply blast
 using add.commute apply blast
apply simp
by (simp add: add.commute)

lemma switching_induction :
  "\<forall>n_one n_two h_one v_one h_two v_two.
            n_one + n_two \<le> k \<longrightarrow>
            finite (FwdValidators s h) \<longrightarrow>
            legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two
             (h_two, v_two) \<longrightarrow>
            (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h') \<Longrightarrow>
         \<forall>n_one n_two h_one v_one h_two v_two.
            n_one + n_two \<le> Suc k \<longrightarrow>
            finite (FwdValidators s h) \<longrightarrow>
            legitimacy_fork_with_center_with_high_root_with_n_switching s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two
             (h_two, v_two) \<longrightarrow>
            (\<exists>h' v'. heir s (h_orig, v_orig) (h', v') \<and> one_third_of_fwd_slashed s h')"
apply clarify
apply (drule sum_suc)
apply (erule disjE)
 apply blast
apply (erule disjE)
  using accountable_safety_from_legitimacy_fork_with_high_root_base apply blast
apply (erule disjE)
 apply clarify
 using switching_induction_case_one apply blast
apply clarify
using switching_induction_case_two apply blast
done

lemma accountable_safety_from_legitimacy_fork_with_high_root_with_n_ind :
"\<forall> n_one n_two h_one v_one h_two v_two.
 n_one + n_two \<le> k \<longrightarrow>
 finite (FwdValidators s h) \<longrightarrow>
 legitimacy_fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<longrightarrow>
 (\<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_fwd_slashed s h')"
apply(induction k)
 using accountable_safety_from_legitimacy_fork_with_high_root_base apply blast
using switching_induction by blast

lemma accountable_safety_from_legitimacy_fork_with_high_root_with_n :
"finite (FwdValidators s h) \<Longrightarrow>
 legitimacy_fork_with_center_with_high_root_with_n_switching
    s (h_orig, v_orig) (h, v) n_one (h_one, v_one) n_two (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
using accountable_safety_from_legitimacy_fork_with_high_root_with_n_ind by blast

lemma accountable_safety_from_legitimacy_fork_with_high_root :
"finite (FwdValidators s h) \<Longrightarrow>
 legitimacy_fork_with_center_with_high_root s (h_orig, v_orig) (h, v) (h_one, v_one) (h_two, v_two) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h_orig, v_orig) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
by (meson accountable_safety_from_legitimacy_fork_with_high_root_with_n legitimacy_fork_with_center_with_high_root_has_n_switching)


lemma accountable_safety_center :
"validator_sets_finite s \<Longrightarrow>
 legitimacy_fork_with_center s (h, v) (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h, v) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
apply(drule legitimacy_fork_with_center_choose_high_root)
apply(clarify)
	using accountable_safety_from_legitimacy_fork_with_high_root validator_sets_finite_def by blast

lemma heir_initial :
   "heir s (h, v) (h1, v1)  \<Longrightarrow>
    heir s (h, v) (h, v)"
apply(induction rule: heir.induct)
  using heir_self apply auto[1]
 apply simp
apply simp
done

lemma legitimacy_fork_with_center_and_root :
  " legitimacy_fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
    legitimacy_fork_with_center s (h, v) (h, v) (h1, v1) (h2, v2)
  "
apply simp
using heir_initial by blast

text "If a situation has a finite number of
      validators on each hash, a legitimacy fork means some validator set suffers 1/3 slashing.
      A legitimacy fork is defined using the @{term heir} relation.  The slashed validator set
      is also a heir of the original validator set.
     "

text "This variant of accountable safety only requires slashing conditions 3 and 4."

lemma accountable_safety_for_legitimacy_fork :
"validator_sets_finite s \<Longrightarrow>
 legitimacy_fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   heir s (h, v) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
using accountable_safety_center legitimacy_fork_with_center_and_root by blast

text "The above theorem only works for forks whose branches are made of the chain of sourcing.
We are now going to turn any forks into such legitimacy forks.  A fork is simply three
hashes that form a forking shape.
"

definition heir_or_self :: "situation \<Rightarrow> (hash \<times> view) \<Rightarrow> (hash \<times> view) \<Rightarrow> bool"
where
"heir_or_self s p0 p1 = (p0 = p1 \<or> heir s p0 p1)"

subsection "Turning Any Fork into Legitimacy-Fork"

lemma inherit_normal_means_ancestor_descendant :
  "inherit_normal s (h', v') (h'', v'') \<Longrightarrow>
   ancestor_descendant s h' h''"
using ancestor_descendant_def by auto

lemma nth_ancestor_trans:
  "\<forall> n h' h h''.
   nth_ancestor s n h' = Some h \<longrightarrow> nth_ancestor s na h'' = Some h' \<longrightarrow>
   nth_ancestor s (na + n) h'' = Some h"
apply(induction na)
 apply simp
apply auto
apply(case_tac "PrevHash s h''"; simp)
done

lemma ancestor_descendant_trans:
  "ancestor_descendant s h h' \<Longrightarrow>
   ancestor_descendant s h' h'' \<Longrightarrow>
   ancestor_descendant s h h''"
apply(auto simp add: ancestor_descendant_def)
apply(rule_tac x = "na + n" in exI)
by (simp add: nth_ancestor_trans)

lemma heir_is_descendant :
  "heir s (h1, v1) (h2, v2) \<Longrightarrow> ancestor_descendant s (fst (h1, v1)) (fst (h2, v2)) "
apply(induction rule: heir.induct)
  apply simp
  using ancestor_descendant_def nth_ancestor.simps(1) apply blast
 apply (metis ancestor_descendant_trans fst_conv inherit_normal_means_ancestor_descendant)
using ancestor_descendant_def nth_ancestor_trans by fastforce

lemma heir_chain_means_same_chain :
  "on_same_heir_chain s (h1, v1) (h2, v2) \<Longrightarrow>
   on_same_chain s h1 h2"
apply(simp add: on_same_heir_chain_def on_same_chain_def)
using heir_is_descendant by auto

lemma prepared_self_is_heir :
 "prepared_by_both s h1 v v1_src \<Longrightarrow>
  ancestor_descendant_with_chosen_validators s (h, v) (h1, v) \<Longrightarrow>
  heir s (h, v) (h1, v)"
proof -
  assume "ancestor_descendant_with_chosen_validators s (h,v) (h1, v)"
  then have "h = h1"
    using ancestor_with_same_view by auto
  assume "prepared_by_both s h1 v v1_src"
  then have "heir s (h1, v) (h1, v)"
    using heir_self by auto
  show "heir s (h, v) (h1, v)"
  	using \<open>h = h1\<close> \<open>heir s (h1, v) (h1, v)\<close> by blast
qed

lemma younger_ancestor :
 "nat (v1 - v) \<le> 0 \<longrightarrow>
  validator_sets_finite s \<longrightarrow>
  prepared_by_both s h1 v1 v1_src \<longrightarrow>
  ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
  heir s (h, v) (h1, v1)"
using ancestor_with_same_view prepared_self_is_heir by fastforce

lemma one_third_of_non_empty :
  "X \<noteq> {} \<Longrightarrow>
   finite X \<Longrightarrow>
   one_third X f \<Longrightarrow>
   \<exists> x. x \<in> X \<and> f x"
apply(simp add: one_third_def)
apply(case_tac " card {n \<in> X. f n} > 0")
 apply (metis (no_types, lifting) Collect_empty_eq card.infinite card_0_eq gr_implies_not_zero)
by force

definition more_than_two_thirds :: "validator set \<Rightarrow> (validator \<Rightarrow> bool) \<Rightarrow> bool"
where
"more_than_two_thirds X f =
   (2 * card X < 3 * card ({n. n \<in> X \<and> f n}))"

lemma not_one_third :
  "finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow>
   (\<not> one_third s f) = (more_than_two_thirds s (\<lambda> n. \<not> f n))"
apply(auto simp add: one_third_def more_than_two_thirds_def)
done

lemma two_thirds_not_one_third:
   "validator_sets_finite s \<Longrightarrow>
    \<not> one_third (RearValidators s h1) (slashed s) \<Longrightarrow>
    two_thirds (RearValidators s h1) (\<lambda>n. (n, Prepare (h1, v1, v1_src)) \<in> Messages s) \<Longrightarrow>
    \<exists>n. n \<in> RearValidators s h1 \<and> \<not> slashed s n \<and> (n, Prepare (h1, v1, v1_src)) \<in> Messages s"
apply(subgoal_tac "two_thirds (RearValidators s h1) (\<lambda> n. \<not> slashed s n)")
 apply(subgoal_tac "one_third (RearValidators s h1) (\<lambda> n. \<not> slashed s n \<and> (n, Prepare (h1, v1, v1_src)) \<in> Messages s)")
  apply(subgoal_tac "RearValidators s h1 \<noteq> {} \<and> finite (RearValidators s h1)")
   using one_third_of_non_empty apply blast
  using validator_sets_finite_def apply blast
 apply (simp add: two_thirds_two_thirds_one_third validator_sets_finite_def)
apply(subgoal_tac "more_than_two_thirds (RearValidators s h1) (\<lambda>n. \<not> slashed s n)")
 apply (simp add: more_than_two_thirds_def two_thirds_def)
using not_one_third validator_sets_finite_def by auto

lemma cutting_prev :
      "ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
       v < v1 \<Longrightarrow>
       PrevHash s h1 = Some a \<Longrightarrow>
       ancestor_descendant_with_chosen_validators s (h, v) (a, v1 - 1)"
apply(erule ancestor_descendant_with_chosen_validators.cases)
 apply simp
apply simp
done

lemma ancestor_descendant_with_chosen_validators_go_back:
   "\<forall> v1 v1_src h v h_anc h1.
    k = nat (v1 - v1_src) \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
    nth_ancestor s (nat (v1 - v1_src)) h1 = Some h_anc \<longrightarrow>
    v \<le> v1_src \<longrightarrow>
    v1_src < v1 \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h_anc, v1_src)"
apply(induction k)
 apply clarify
 apply simp
apply clarsimp
apply(subgoal_tac
 "(case PrevHash s h1 of
      None \<Rightarrow> None
    | Some h' \<Rightarrow> nth_ancestor s k h') = Some h_anc")
 apply(case_tac "PrevHash s h1")
  apply simp
 apply simp
 apply(drule_tac x = "v1 - 1" in spec)
 apply(drule_tac x = "v1_src" in spec)
 apply(subgoal_tac "k = nat (v1 - 1 - v1_src)")
  apply simp
  apply(drule_tac x = h in spec)
  apply(drule_tac x = v in spec)
  apply(drule_tac x = h_anc in spec)
  apply(drule_tac x = a in spec)
  apply simp
  apply(case_tac "v1_src < v1 - 1")
   apply(subgoal_tac "ancestor_descendant_with_chosen_validators s (h, v) (a, v1 - 1)")
    apply blast
   apply (simp add: cutting_prev)
  apply(subgoal_tac "v1_src = v1 - 1")
   apply simp
   apply(erule ancestor_descendant_with_chosen_validators.cases)
    apply simp
   apply simp
  apply simp
 apply linarith
by (metis nth_ancestor.simps(2))

lemma tmp:
  "committed_by_both s h1a v1a \<Longrightarrow>
   committed_by_both s h1a (v1a + 1 - 1)"
apply simp
done

lemma ancestor_of_parent :
      "nth_ancestor s (nat (v1 - v1_src)) h1 = Some h_anc \<Longrightarrow>
       PrevHash s h1 = Some h_prev \<Longrightarrow>
       v1 > v1_src \<Longrightarrow>
       nth_ancestor s (nat (v1 - 1 - v1_src)) h_prev = Some h_anc"
apply(case_tac "nat (v1 - v1_src)")
 apply simp
apply simp
proof -
  fix nata :: nat
  assume "v1_src < v1"
  assume a1: "nat (v1 - v1_src) = Suc nata"
  assume a2: "nth_ancestor s nata h_prev = Some h_anc"
  have "nat (- 1 + v1 + - 1 * v1_src) = nata"
    using a1 by linarith
  then show ?thesis
    using a2 by simp
qed


lemma ancestor_descendant_shorter :
   "\<forall> v1 h1 v1_src h_anc.
    nat (v1 - v) = k \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
    nth_ancestor s (nat (v1 - v1_src)) h1 = Some h_anc \<longrightarrow>
    v1_src < v1 \<longrightarrow>
    v \<le> v1_src \<longrightarrow> ancestor_descendant_with_chosen_validators s (h_anc, v1_src) (h1, v1)"
apply(induction k)
 apply simp
apply clarify
apply(case_tac "v1_src = v1 - 1")
 apply simp
 apply(case_tac "PrevHash s h1")
  apply simp
 apply simp
 apply(erule ancestor_descendant_with_chosen_validators.cases)
  apply simp
 apply(subgoal_tac "prev_next_with_chosen_validators s (h_anc, v1 - 1) (h1, v1)")
  using inheritance_self inheritances_step apply blast
 apply clarify
 apply(simp only: prev_next_with_chosen_validators.simps)
 apply(rule conjI)
  apply blast
 apply(rule conjI)
  apply linarith
 apply(erule conjE)
 apply(erule conjE)
 apply(erule disjE)
  apply(rule disjI1)
  apply blast
 apply(rule disjI2)
 apply(subgoal_tac "h_anc = h1a")
  apply(rule conjI)
   apply blast
  apply(subgoal_tac "committed_by_both s h1a (v1a + 1 - 1)")
   apply blast
  apply(rule tmp)
  apply blast
 apply blast
apply(drule_tac x = "v1 - 1" in spec)
apply(subgoal_tac "\<exists> h_prev. PrevHash s h1 = Some h_prev")
 apply clarify
 apply(drule_tac x = h_prev in spec)
 apply(drule_tac x = v1_src in spec)
 apply(drule_tac x = h_anc in spec)
 apply(subgoal_tac "nat (v1 - 1 - v) = k")
  apply(subgoal_tac "ancestor_descendant_with_chosen_validators s (h, v) (h_prev, v1 - 1)")
   apply(subgoal_tac " nth_ancestor s (nat (v1 - 1 - v1_src)) h_prev = Some h_anc")
    apply(subgoal_tac "v1_src < v1 - 1")
     apply(subgoal_tac " ancestor_descendant_with_chosen_validators s (h_anc, v1_src) (h_prev, v1 - 1)")
      apply(rule_tac  inheritances_step)
       apply blast
      apply(simp)
      apply(erule ancestor_descendant_with_chosen_validators.cases)
       apply simp
      apply simp
     apply blast
    apply linarith
   using ancestor_of_parent apply blast
  apply (simp add: cutting_prev)
 apply linarith
apply(case_tac "nat (v1 - v1_src)")
 apply simp
apply simp
apply(case_tac "PrevHash s h1"; auto)
done


lemma no_commits_in_between_induction :
   "\<forall> v1 h1.
    nat (v1 - v) \<le> Suc k \<longrightarrow>
    validator_sets_finite s \<longrightarrow>
    committed_by_both s h v \<longrightarrow>
    v \<noteq> v1 \<longrightarrow>
    v1_src < v \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
    (\<forall>v>v1_src.
       nat (v1 - v) \<le> k \<longrightarrow>
       (\<forall>h. committed_by_both s h v \<longrightarrow> v = v1 \<or> \<not> ancestor_descendant_with_chosen_validators s (h, v) (h1, v1))) \<longrightarrow>
    v < v1 \<and> (validators_match s h h1 \<or> validators_change s h h1)"
apply(induction k)
 apply clarify
 apply (rule conjI)
  apply auto[1]
 apply(erule ancestor_descendant_with_chosen_validators.cases)
  apply simp
 using ancestor_with_same_view apply fastforce
apply clarsimp
apply(rule conjI)
 apply auto[1]
apply(erule ancestor_descendant_with_chosen_validators.cases)
 apply simp
apply clarsimp
apply(case_tac " committed_by_both s h1a v1a ")
 apply simp
 apply(rotate_tac 5)
 apply(drule_tac x = v1a in spec)
 apply(subgoal_tac "v1_src < v1a")
  apply(subgoal_tac " nat (v1a + 1 - v1a) \<le> Suc k")
   apply simp
   apply(drule_tac x = h1a in spec)
   apply simp
   apply(subgoal_tac "ancestor_descendant_with_chosen_validators s (h1a, v1a) (h2, v1a + 1)")
    apply blast
   using inheritance_self inheritances_step prev_next_with_chosen_validators.simps apply blast
  apply linarith
 apply(subgoal_tac "v \<le> v1a")
  apply linarith
 using ancestor_with_same_view apply auto[1]
apply(subgoal_tac "validators_match s h h1a \<or> validators_change s h h1a")
 using validators_change_def validators_match_def apply auto[1]
apply(drule_tac x = v1a in spec)
apply(subgoal_tac "nat (v1a - v) \<le> Suc k")
 apply(subgoal_tac "v \<noteq> v1a")
  apply simp
  apply(drule_tac x = h1a in spec)
  apply(subgoal_tac "\<forall>v>v1_src.
           nat (v1a - v) \<le> k \<longrightarrow>
           (\<forall>h. committed_by_both s h v \<longrightarrow> v = v1a \<or> \<not> ancestor_descendant_with_chosen_validators s (h, v) (h1a, v1a))")
   apply simp
  apply(rule allI)
  apply(case_tac " v1_src < va")
   apply simp
   apply(case_tac "nat (v1a - va) \<le> k")
    apply simp
    apply(rule allI)
    apply(rule impI)
    apply(drule_tac x = va in spec)
    apply simp
    apply(case_tac "nat (v1a + 1 - va) \<le> Suc k")
     apply simp
     apply(drule_tac x = ha in spec)
     apply simp
     apply(erule disjE)
      apply simp
      apply(subgoal_tac "\<not> v1a + 1 \<le> v1a")
       apply (metis ancestor_with_same_view prod.sel(2))
      apply simp
     using inheritances_step prev_next_with_chosen_validators.simps apply blast
    apply linarith
   apply blast
  apply blast
 using ancestor_with_same_view apply fastforce
by linarith


lemma no_commits_in_between :
  "nat (v1 - v) \<le> Suc k \<longrightarrow>
   validator_sets_finite s \<longrightarrow>
   committed_by_both s h v \<longrightarrow>
   prepared_by_both s h1 v1 v1_src \<longrightarrow>
   - 1 \<le> v1_src \<longrightarrow>
   v \<noteq> v1 \<longrightarrow>
   v1_src < v1 \<longrightarrow>
   v1_src < v \<longrightarrow>
   ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
   (\<nexists>v h. nat (v1 - v) \<le> k \<and>
         validator_sets_finite s \<and>
         committed_by_both s h v \<and>
         prepared_by_both s h1 v1 v1_src \<and>
         - 1 \<le> v1_src \<and>
         v \<noteq> v1 \<and> v1_src < v1 \<and> v1_src < v \<and> ancestor_descendant_with_chosen_validators s (h, v) (h1, v1)) \<longrightarrow>
   committed_by_both s h v \<and>
   ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<and>
   v1_src < v \<and> v < v1 \<and> (validators_match s h h1 \<or> validators_change s h h1)"
apply clarsimp
using no_commits_in_between_induction by blast


lemma pick_max_induction' :
   "\<forall> v h.
    nat (v1 - v) \<le> k \<longrightarrow>
    validator_sets_finite s \<longrightarrow>
    committed_by_both s h v \<longrightarrow>
    prepared_by_both s h1 v1 v1_src \<longrightarrow>
    - 1 \<le> v1_src \<longrightarrow>
    v \<noteq> v1 \<longrightarrow>
    v1_src < v1 \<longrightarrow>
    v1_src < v \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
    (\<exists>h_max v_max.
       committed_by_both s h_max v_max \<and>
       ancestor_descendant_with_chosen_validators s (h_max, v_max) (h1, v1) \<and>
       v1_src < v_max \<and> v_max < v1 \<and> (validators_match s h_max h1 \<or> validators_change s h_max h1))"
apply(induction k)
 using ancestor_with_same_view apply fastforce
apply clarify
apply(case_tac
  "\<exists> v h. nat (v1 - v) \<le> k \<and>
          validator_sets_finite s \<and>
          committed_by_both s h v \<and>
          prepared_by_both s h1 v1 v1_src \<and>
          - 1 \<le> v1_src \<and> 
          v \<noteq> v1 \<and>
          v1_src < v1 \<and>
          v1_src < v \<and>
          ancestor_descendant_with_chosen_validators s (h, v) (h1, v1)")
 apply blast
apply(rule_tac x = h in exI)
apply(rule_tac x = v in exI)
using no_commits_in_between by blast

lemma pick_max_induction :
   "nat (v1 - v) = k \<longrightarrow>
    validator_sets_finite s \<longrightarrow>
    committed_by_both s h v \<longrightarrow>
    prepared_by_both s h1 v1 v1_src \<longrightarrow>
    - 1 \<le> v1_src \<longrightarrow>
    v \<noteq> v1 \<longrightarrow>
    v1_src < v1 \<longrightarrow>
    v1_src < v \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
    (\<exists>h_max v_max.
       committed_by_both s h_max v_max \<and>
       ancestor_descendant_with_chosen_validators s (h_max, v_max) (h1, v1) \<and>
       v1_src < v_max \<and> v_max < v1 \<and> (validators_match s h_max h1 \<or> validators_change s h_max h1))"
using pick_max_induction' apply blast
done

lemma pick_max :
   "validator_sets_finite s \<longrightarrow>
    committed_by_both s h v \<longrightarrow>
    prepared_by_both s h1 v1 v1_src \<longrightarrow>
    - 1 \<le> v1_src \<longrightarrow>
    v \<noteq> v1 \<longrightarrow>
    v1_src < v1 \<longrightarrow>
    v1_src < v \<longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
    (\<exists>h_max v_max.
       committed_by_both s h_max v_max \<and>
       ancestor_descendant_with_chosen_validators s (h_max, v_max) (h1, v1) \<and>
       v1_src < v_max \<and> v_max < v1 \<and> (validators_match s h_max h1 \<or> validators_change s h_max h1))"
	by (simp add: pick_max_induction)

lemma slashing_three_aux' :
   "finite (RearValidators s h1) \<Longrightarrow>
    one_third (RearValidators s h1)
     (\<lambda>n. (n, Commit (h_max, v_max)) \<in> Messages s \<and>
           (n, Prepare (h1, v1, v1_src)) \<in> Messages s \<and> v1_src < v_max \<and> v_max < v1) \<Longrightarrow>
    one_third (RearValidators s h1)
     (\<lambda>n. \<exists>x y v w u. (n, Commit (x, v)) \<in> Messages s \<and> (n, Prepare (y, w, u)) \<in> Messages s \<and> u < v \<and> v < w)"
apply(rule one_third_mp)
  apply simp
 defer
 apply blast
apply blast
done

lemma using_max :
      "validator_sets_finite s \<Longrightarrow>
       committed_by_both s h v \<Longrightarrow>
       prepared_by_both s h1 v1 v1_src \<Longrightarrow>
       - 1 \<le> v1_src \<Longrightarrow>
       v1_src < v1 \<Longrightarrow>
       ancestor_descendant_with_chosen_validators s (h_max, v_max) (h1, v1) \<Longrightarrow>
       committed_by_both s h_max v_max \<Longrightarrow>
       v1_src < v_max \<Longrightarrow>
       v_max < v1 \<Longrightarrow> validators_match s h_max h1 \<or> validators_change s h_max h1 \<Longrightarrow> 
       one_third_of_fwd_or_rear_slashed s h1"
apply(subgoal_tac "one_third (RearValidators s h1) (slashed_three s)")
 apply (meson one_third_mp one_third_of_fwd_or_rear_slashed_def one_third_of_rear_slashed_def slashed_def validator_sets_finite_def)
apply(subgoal_tac
   "one_third (RearValidators s h1)
    (\<lambda> n. (\<exists> x y v w u.
      (n, Commit (x, v)) \<in> Messages s \<and>
      (n, Prepare (y, w, u)) \<in> Messages s \<and>
      u < v \<and> v < w))")
 using slashed_three_def apply presburger
apply(subgoal_tac "    one_third (RearValidators s h1)
     (\<lambda>n. (n, Commit (h_max, v_max)) \<in> Messages s \<and> (n, Prepare (h1, v1, v1_src)) \<in> Messages s \<and>
           v1_src < v_max \<and> v_max < v1)")
 apply(rule slashing_three_aux')
  using validator_sets_finite_def apply blast
 apply blast
apply(rule two_thirds_two_thirds_one_third)
  using validator_sets_finite_def apply blast
 apply(erule disjE)
  apply(subgoal_tac "two_thirds (RearValidators s h_max) (\<lambda>x. (x, Commit (h_max, v_max)) \<in> Messages s)")
   apply (simp add: validators_match_def)
  apply(simp add: committed_by_both_def committed_by_rear_def committed_def two_thirds_sent_message_def)
 apply(subgoal_tac "two_thirds (FwdValidators s h_max) (\<lambda>x. (x, Commit (h_max, v_max)) \<in> Messages s)")
  apply (simp add: validators_change_def)
 apply(simp add: committed_by_both_def committed_by_fwd_def committed_def two_thirds_sent_message_def)
apply(simp add: prepared_by_both_def prepared_by_rear_def prepared_def two_thirds_sent_message_def)
done

lemma commit_skipping :
   "validator_sets_finite s \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
    prepared_by_both s h1 v1 v1_src \<Longrightarrow>
    - 1 \<le> v1_src \<Longrightarrow>
    v \<noteq> v1 \<Longrightarrow>
    v1_src < v1 \<Longrightarrow>
    v1_src < v \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
    one_third_of_fwd_or_rear_slashed s h1
"
apply(subgoal_tac
    "\<exists> h_max v_max. committed_by_both s h_max v_max \<and>
                    ancestor_descendant_with_chosen_validators s (h_max, v_max) (h1, v1) \<and>
                       v1_src < v_max \<and>
                       v_max < v1 \<and>
                       (validators_match s h_max h1 \<or> validators_change s h_max h1)
    ")
 apply clarify
 using using_max apply blast
by (simp add: pick_max)

lemma slashed_two_essense :
  "validator_sets_finite s \<Longrightarrow>
    prepared_by_both s h1 v1 v1_src \<Longrightarrow>
    v1_src < v1 \<Longrightarrow>
    0 \<le> v \<Longrightarrow>
    - 1 < v1_src \<Longrightarrow>
    \<not> one_third (RearValidators s h1) (slashed s) \<Longrightarrow>
    prepared_by_rear s h1 v1 v1_src \<Longrightarrow> \<exists>h_anc. sourcing s h_anc (h1, v1, v1_src)"
apply(subgoal_tac "\<not> one_third (RearValidators s h1) (slashed_two s)")
 apply(subgoal_tac "\<exists> n. n \<in> RearValidators s h1 \<and> \<not> slashed_two s n \<and> (n, Prepare (h1, v1, v1_src)) \<in> Messages s")
  using slashed_two_def apply blast
 apply(subgoal_tac "0 < card {n. n \<in> RearValidators s h1 \<and> \<not> slashed_two s n \<and> (n, Prepare (h1, v1, v1_src)) \<in> Messages s}")
  apply (metis (no_types, lifting) Collect_empty_eq card_0_eq card_infinite less_not_refl2)
 apply(subgoal_tac "one_third (RearValidators s h1) (\<lambda> n.  (\<not> slashed_two s n) \<and> (n, Prepare (h1, v1, v1_src)) \<in> Messages s)")
  apply(subgoal_tac "0 < card (RearValidators s h1)")
   apply(simp add: one_third_def)
  using card_gt_0_iff validator_sets_finite_def apply auto[1]
 apply(subgoal_tac "two_thirds (RearValidators s h1) (\<lambda>n. (n, Prepare (h1, v1, v1_src)) \<in> Messages s)")
  apply(subgoal_tac "two_thirds (RearValidators s h1) (\<lambda>n. \<not> slashed_two s n)")
   apply(rule two_thirds_two_thirds_one_third)
     using validator_sets_finite_def apply blast
    apply blast
   apply blast
  using more_than_two_thirds_def not_one_third two_thirds_def validator_sets_finite_def apply auto[1]
 using prepared_by_rear_def prepared_def two_thirds_sent_message_def apply auto[1]
by (meson one_third_mp slashed_def validator_sets_finite_def)


lemma use_slashed_two :
 "  validator_sets_finite s \<Longrightarrow>
    prepared_by_both s h1 v1 v1_src \<Longrightarrow>
    committed_by_both s h v \<Longrightarrow>
     v \<noteq> v1 \<Longrightarrow>
    v1_src < v1 \<Longrightarrow>
    0 \<le> v \<Longrightarrow>
    ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
    \<forall>h'. (\<forall>v'. \<not> ancestor_descendant_with_chosen_validators s (h, v) (h', v')) \<or> \<not> one_third_of_fwd_or_rear_slashed s h' \<Longrightarrow>
    - 1 < v1_src \<Longrightarrow>
    \<not> one_third (RearValidators s h1) (slashed s) \<Longrightarrow>
    prepared_by_rear s h1 v1 v1_src \<Longrightarrow>
    \<exists>h_src srcsrc.
       prepared_by_both s h_src v1_src srcsrc \<and>
       - 1 \<le> srcsrc \<and>
       srcsrc < v1_src \<and> ancestor_descendant_with_chosen_validators s (h, v) (h_src, v1_src) \<and> heir s (h_src, v1_src) (h1, v1)"
apply(subgoal_tac "\<exists> h_anc. sourcing s h_anc (h1, v1, v1_src)")
 apply clarify
 apply(simp only: sourcing_def sourcing_normal.simps sourcing_switching_validators.simps)
 apply(erule disjE)
  apply clarify
  apply(rule_tac x = h_anc in exI)
  apply(rule_tac x = v_ss in exI)
  apply(rule conjI)
   apply simp
  apply(rule conjI)
   apply simp
  apply (rule conjI)
   apply simp
  apply(case_tac "v \<le> v1_src")
   apply(rule conjI)
    using ancestor_descendant_with_chosen_validators_go_back apply blast
   apply(rule_tac h' = h_anc and v' = v1_src in heir_normal_step)
     using heir_self apply blast
    apply auto[1]
   using ancestor_descendant_shorter apply blast
  apply(subgoal_tac "one_third_of_fwd_or_rear_slashed s h1")
   apply blast
  apply (simp add: commit_skipping)
 apply clarify
 apply(rule_tac x = h_anc in exI)
 apply(rule_tac x = v_ss in exI)
 apply(rule conjI)
  apply simp
 apply(rule conjI)
  apply simp
 apply (rule conjI)
  apply simp
 apply(case_tac "v \<le> v1_src")
  apply(rule conjI)
   using ancestor_descendant_with_chosen_validators_go_back apply blast
  apply(rule_tac h' = h_anc and v' = v1_src in heir_switching_step)
    using heir_self apply blast
   apply auto[1]
  using ancestor_descendant_shorter apply blast
 apply(subgoal_tac "one_third_of_fwd_or_rear_slashed s h1")
  apply blast
 apply (simp add: commit_skipping)
using slashed_two_essense by blast


lemma induction_step_following_back_history:
      "\<forall>v1 h1 v1_src.
          nat (v1 - v) \<le> k \<longrightarrow>
          validator_sets_finite s \<longrightarrow>
          committed_by_both s h v \<longrightarrow>
          prepared_by_both s h1 v1 v1_src \<longrightarrow>
          - 1 \<le> v1_src \<longrightarrow>
          v1_src < v1 \<longrightarrow>
          0 \<le> v \<longrightarrow>
          ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
          heir s (h, v) (h1, v1) \<or>
          (\<exists>h' v'. ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and> one_third_of_fwd_or_rear_slashed s h') \<Longrightarrow>
       nat (v1 - v) \<le> Suc k \<Longrightarrow>
       validator_sets_finite s \<Longrightarrow>
       committed_by_both s h v \<Longrightarrow>
       prepared_by_both s h1 v1 v1_src \<Longrightarrow>
       - 1 \<le> v1_src \<Longrightarrow>
       v1_src < v1 \<Longrightarrow>
       0 \<le> v \<Longrightarrow>
       ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
       \<nexists>h' v'. ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and> one_third_of_fwd_or_rear_slashed s h' \<Longrightarrow>
       heir s (h, v) (h1, v1)"
apply(case_tac "v = v1")
 defer
 apply(case_tac "-1 < v1_src")
  apply(subgoal_tac
   "\<exists> h_src srcsrc.
     prepared_by_both s h_src v1_src srcsrc \<and>
     -1 \<le> srcsrc \<and>
     srcsrc < v1_src \<and>
     0 \<le> v \<and>
     ancestor_descendant_with_chosen_validators s (h, v) (h_src, v1_src) \<and>
     heir s (h_src, v1_src) (h1, v1)
   ")
   apply clarify
   apply(drule_tac x = v1_src in spec)
   apply(drule_tac x = h_src in spec)
   apply(drule_tac x = srcsrc in spec)
   apply clarsimp
   apply(subgoal_tac " nat (v1_src - v) \<le> k ")
    using heir_trans apply blast
   apply linarith
  apply(case_tac "one_third_of_rear_slashed s h1")
   using one_third_of_fwd_or_rear_slashed_def apply blast
  apply(simp add: one_third_of_rear_slashed_def)
  apply(subgoal_tac "prepared_by_rear s h1 v1 v1_src")
   using use_slashed_two apply blast
  using prepared_by_both_def apply blast
 apply(subgoal_tac "v1_src < v")
  apply(subgoal_tac "one_third_of_fwd_or_rear_slashed s h1")
   apply blast
  using commit_skipping apply blast
 apply linarith
using prepared_self_is_heir apply blast
done


lemma follow_back_history_with_prepares_ind :
  "\<forall> v1 h1 v1_src.
   nat (v1 - v) \<le> k \<longrightarrow>
   validator_sets_finite s \<longrightarrow>
   committed_by_both s h v \<longrightarrow>
   prepared_by_both s h1 v1 v1_src \<longrightarrow>
   -1 \<le> v1_src \<longrightarrow>
   v1_src < v1 \<longrightarrow>
   v \<ge> 0 \<longrightarrow>
   ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<longrightarrow>
   heir s (h, v) (h1, v1) \<or>
   (\<exists> h' v'.
     ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
     one_third_of_fwd_or_rear_slashed s h')"
apply(induction k)
 apply (simp add: younger_ancestor)
apply clarify
using induction_step_following_back_history by blast

lemma follow_back_history_with_prepares :
  "validator_sets_finite s \<Longrightarrow>
   committed_by_both s h v \<Longrightarrow>
   prepared_by_both s h1 v1 v1_src \<Longrightarrow>
   -1 \<le> v1_src \<Longrightarrow>
   v1_src < v1 \<Longrightarrow>
   0 \<le> v \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
   heir s (h, v) (h1, v1) \<or>
   (\<exists> h' v'.
     ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
     one_third_of_fwd_or_rear_slashed s h')"
using follow_back_history_with_prepares_ind apply blast
done


lemma slashed_one_on_rear': "
 validator_sets_finite s \<Longrightarrow>
    committed_by_rear s h1 v1 \<Longrightarrow>
   (\<exists>v1_src. -1 \<le> v1_src \<and> v1_src < v1 \<and> prepared_by_both s h1 v1 v1_src) \<or> 
    one_third (RearValidators s h1) (slashed_one s)"
apply(simp add: committed_by_rear_def committed_def two_thirds_sent_message_def)
by (metis (no_types, lifting) one_third_mp slashed_one_def two_thirds_two_thirds_one_third validator_sets_finite_def)


lemma slashed_one_on_rear :
  "validator_sets_finite s \<Longrightarrow>
   committed_by_rear s h1 v1 \<Longrightarrow>
   (\<exists>v1_src. -1 \<le> v1_src \<and> v1_src < v1 \<and> prepared_by_both s h1 v1 v1_src) \<or> one_third_of_rear_slashed s h1"
apply(simp add: one_third_of_rear_slashed_def)
by (metis one_third_mp slashed_def slashed_one_on_rear' validator_sets_finite_def)


lemma slashed_one_on_descendant_with_chosen_validators' :
  "validator_sets_finite s \<Longrightarrow>
   committed_by_both s h1 v1 \<Longrightarrow>
   (\<exists> v1_src. -1 \<le> v1_src \<and> v1_src < v1 \<and> prepared_by_both s h1 v1 v1_src) \<or>
   one_third_of_fwd_or_rear_slashed s h1"
apply(simp add: committed_by_both_def one_third_of_fwd_or_rear_slashed_def)
using slashed_one_on_rear by auto

lemma slashed_one_on_descendant_with_chosen_validators :
  "validator_sets_finite s \<Longrightarrow>
   committed_by_both s h v \<Longrightarrow>
   committed_by_both s h1 v1 \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
   (\<exists> v1_src. -1 \<le> v1_src \<and> v1_src < v1 \<and> prepared_by_both s h1 v1 v1_src) \<or>
   (\<exists> h' v'.
     ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
     one_third_of_fwd_or_rear_slashed s h')"
using slashed_one_on_descendant_with_chosen_validators' by blast

lemma follow_back_history :
  "validator_sets_finite s \<Longrightarrow>
   committed_by_both s h v \<Longrightarrow>
   committed_by_both s h1 v1 \<Longrightarrow>
   0 \<le> v \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h, v) (h1, v1) \<Longrightarrow>
   heir s (h, v) (h1, v1) \<or>
   (\<exists> h' v'.
     ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
     one_third_of_fwd_or_rear_slashed s h')"
using follow_back_history_with_prepares slashed_one_on_descendant_with_chosen_validators' by blast



lemma fork_contains_legitimacy_fork :
"validator_sets_finite s \<Longrightarrow>
 0 \<le> v \<Longrightarrow>
 fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 legitimacy_fork_with_commits s (h, v) (h1, v1) (h2, v2) \<or>
 (\<exists> h' v'.
   ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
   one_third_of_fwd_or_rear_slashed s h')"
apply(simp only: fork_with_commits.simps legitimacy_fork_with_commits.simps legitimacy_fork.simps fork.simps)
using follow_back_history heir_chain_means_same_chain by blast



lemma heir_means_ad_inheritance :
  "heir s (h, v) (h', v') \<Longrightarrow>
   ancestor_descendant_with_chosen_validators s (h, v) (h', v')
  "
apply(induction rule: heir.induct)
  apply (simp add: inheritance_self)
 using ancestor_descendant_with_chosen_validators_trans apply blast
using ancestor_descendant_with_chosen_validators_trans by blast

lemma accountable_safety_for_legitimacy_fork_weak :
"validator_sets_finite s \<Longrightarrow>
 v \<ge> 0 \<Longrightarrow>
 legitimacy_fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
   one_third_of_fwd_slashed s h'"
using accountable_safety_for_legitimacy_fork heir_means_ad_inheritance by blast


section "Accountable Safety for Any Fork with Commits (not skippable)"

text "Accountable safety states that, if there is a fork with commits, there is some legitimate heir
of the validator sets of the root, of which 2/3 are slashed.
"

lemma accountable_safety :
"validator_sets_finite s \<Longrightarrow>
 v \<ge> 0 \<Longrightarrow>
 fork_with_commits s (h, v) (h1, v1) (h2, v2) \<Longrightarrow>
 \<exists> h' v'.
   ancestor_descendant_with_chosen_validators s (h, v) (h', v') \<and>
   one_third_of_fwd_or_rear_slashed s h'"
  using accountable_safety_for_legitimacy_fork_weak fork_contains_legitimacy_fork one_third_of_fwd_or_rear_slashed_def by blast


end
