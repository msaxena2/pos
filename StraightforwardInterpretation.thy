theory StraightforwardInterpretation

(* This file is the most straightforward instantiation of
   DynamicValidatorSetOneMessage.casper
   We assume a static validator set consisting of five integers.
 *)

imports DynamicValidatorSetOneMessage

begin

(* I need member_1, member_2 and hash_parent *)

definition validators :: "int set" where
"validators = {1, 2, 3, 4, 5}"

definition powset :: "int set set" where
"powset = Pow validators"

(*
value "powset"
"{{2, 3, 4, 5}, {2, 3, 4}, {2, 3}, {2, 3, 5}, {2, 5}, {2}, {2, 4}, {2, 4, 5}, {4, 5},
  {4}, {}, {5}, {3, 5}, {3}, {3, 4}, {3, 4, 5}, {1, 3, 4, 5}, {1, 3, 4}, {1, 3},
  {1, 3, 5}, {1, 5}, {1}, {1, 4}, {1, 4, 5}, {1, 2, 4, 5}, {1, 2, 4}, {1, 2}, {1, 2, 5},
  {1, 2, 3, 5}, {1, 2, 3}, {1, 2, 3, 4}, {1, 2, 3, 4, 5}}"
*)

lemma validators_is_in_powset : "validators \<in> powset"
  by(auto simp add: powset_def)

lemma more_than_four_validators : "4 \<le> card validators"
  by(simp add: validators_def)

typedef big_quorum = "{ s | s. s \<in> powset \<and> card s \<ge> 4 }"
  apply(rule_tac x = validators in exI; auto)
   apply (simp add: validators_is_in_powset)
  by (simp add: more_than_four_validators)

definition member_2 :: "int \<Rightarrow> big_quorum \<Rightarrow> int set \<Rightarrow> bool" where
"member_2 v bq whole \<equiv> (whole = validators \<and> v \<in> Rep_big_quorum bq)"

typedef small_quorum = "{ s | s. s \<in> powset \<and> card s \<ge> 2 }"
  apply(rule_tac x = validators in exI; auto)
   apply (simp add: validators_is_in_powset)
  by(simp add: validators_def)

definition member_1 :: "int \<Rightarrow> small_quorum \<Rightarrow> int set \<Rightarrow> bool" where
"member_1 v sq whole \<equiv> (whole = validators \<and> v \<in> Rep_small_quorum sq)"

definition hash_parent :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"hash_parent parent child \<equiv> (child = Suc parent)"

lemma no_refl: "hash_parent h2 h2 \<Longrightarrow> False"
  by (simp add: hash_parent_def)

lemma unique_parent: "hash_parent h2 h1 \<Longrightarrow> hash_parent h3 h1 \<Longrightarrow> h2 = h3"
  by (simp add: hash_parent_def)


lemma rep_abs_small:
  "x \<in> {s |s. s \<in> powset \<and> 2 \<le> card s} \<Longrightarrow>
   Rep_small_quorum (Abs_small_quorum x) = x"
  using Abs_small_quorum_inverse by blast

lemma intersection_is_powset:
  "Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2 \<in> powset"
  apply(auto simp add: powset_def)
  using Rep_big_quorum powset_def by auto

lemma big_quorum_is_finite:
  "finite (Rep_big_quorum bq1)"
  by (metis (no_types, lifting) Rep_big_quorum card.infinite le_0_eq mem_Collect_eq rel_simps(76))

lemma quorum_union_is_still_validators:
  "(Rep_big_quorum bq1 \<union> Rep_big_quorum bq2) \<subseteq> validators"
  using Rep_big_quorum powset_def by auto

lemma card_validators: "card validators = 5"
  by (simp add: validators_def)

lemma quorum_union_is_small:
  "card (Rep_big_quorum bq1 \<union> Rep_big_quorum bq2) \<le> 5"
  by (metis card.infinite card_mono card_validators quorum_union_is_still_validators rel_simps(76))

lemma each_big_is_big: "4 \<le> card (Rep_big_quorum bq1)"
  using Rep_big_quorum by blast

lemma uni_inter:
  "card (Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2) + card (Rep_big_quorum bq1 \<union> Rep_big_quorum bq2) =
   card (Rep_big_quorum bq1) + card (Rep_big_quorum bq2)"
  by (metis big_quorum_is_finite card_Un_Int semiring_normalization_rules(24))

lemma uni_inter_sum:
  "card (Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2) + card (Rep_big_quorum bq1 \<union> Rep_big_quorum bq2) \<ge> 8"
  by (metis add_mono_thms_linordered_semiring(1) each_big_is_big numeral_Bit0 uni_inter)


lemma intersection_is_big':
  "8 - card (Rep_big_quorum bq1 \<union> Rep_big_quorum bq2) \<le> card (Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2)"
  using le_diff_conv uni_inter_sum by blast

lemma eight_minus_u:
  "3 \<le> 8 - card (Rep_big_quorum bq1 \<union> Rep_big_quorum bq2)"
  by (smt One_nat_def Suc_leI add.right_neutral add_Suc_right add_diff_cancel_left' antisym_conv big_quorum_is_finite card_mono each_big_is_big finite_Un le_iff_add le_trans linorder_not_le numeral_Bit0 numeral_Bit1 one_add_one plus_nat.simps(2) quorum_union_is_small sup.cobounded1)

lemma intersection_is_big:
  "3 \<le> card (Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2)"
  by (metis eight_minus_u inf.orderE intersection_is_big' le_infE)

lemma quorum_intersection_big:
  "Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2 \<in> {s |s. s \<in> powset \<and> 2 \<le> card s}"
  apply(auto)
   apply (simp add: intersection_is_powset)
  using intersection_is_big linear order_trans by fastforce

lemma quorum_intersection_smaller:
  "member_1 v (Abs_small_quorum (Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2)) vs \<Longrightarrow>
         member_2 v bq1 vs"
  apply(auto simp add: member_1_def member_2_def)
  using quorum_intersection_big rep_abs_small by auto

lemma intersection: "
  \<exists>sq. \<forall>v. member_1 v sq vs \<longrightarrow> member_2 v bq1 vs \<and> member_2 v bq2 vs"
  apply(rule_tac x = "Abs_small_quorum
    (Rep_big_quorum bq1 \<inter> Rep_big_quorum bq2)" in exI; auto)
   using quorum_intersection_smaller apply auto[1]
  by (metis inf_sup_aci(1) quorum_intersection_smaller)

interpretation easy: casper member_1 member_2 hash_parent 0 "\<lambda> _. validators" "\<lambda> _. validators" "\<lambda> _. validators"
  apply(auto simp add: casper_def)
    using no_refl apply blast
     apply (simp add: unique_parent)
    apply(simp add: intersection)
  done

thm easy.accountable_safety
(*
easy.fork ?s ?h0.0 ?epoch0.0 ?m0.0 ?h1.0 ?epoch1.0 ?m1.0 \<Longrightarrow>
\<exists>h epoch m q. easy.justified ?s h epoch m \<and> easy.one_third_of_fwd_or_bwd_slashed ?s h q
*)

end
