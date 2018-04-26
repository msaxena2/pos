theory BlockForestInterpretation

imports Main DynamicValidatorSetOneMessage

(* source *)
(* https://github.com/palmskog/caspertoychain/blob/master/Core/Blockforest.v
 * Version not fixed yet while everything is in flux.
 *)

(* translation *)
(* Remove as much type variables as possible.  Reason: it's impossible to instantiate
   the locale (in DynamicValidatorSetOneMessage.thy) with types containing variables.
   Axioms are fine.  Typedecls are also fine.
 *)

begin

typedecl timestamp
typedecl hash
(* typedecl vProof // no chance of instantiating this as an Isabelle proof *)
typedecl nodeId
typedecl address

type_synonym validatorIndex = nat
type_synonym wei = nat
type_synonym epoch = nat
type_synonym dynasty = nat

typedecl signature

record deposit =
  deposit_validation_addr :: address
  deposit_withdrwawal_addr :: address
  deposit_amount :: wei

record vote =
  vote_validator_index :: validatorIndex
  vote_target_hash :: hash
  vote_target_epoch :: epoch
  vote_source_epoch :: epoch
  vote_sig :: signature

record logout =
  logout_validator_index :: validatorIndex
  logout_epoch :: epoch
  logout_sig ::signature

type_synonym sender = address (* any need to treat NullSender specially?  *)

datatype contractCall = DepositCall deposit 
  | VoteCall vote
  | LogoutCall logout
  | WithdrawCall validatorIndex
  | InitializeEpochCall epoch
  | SlashCall "vote \<times> vote"

record transaction =
  tx_sender :: sender
  tx_call :: contractCall

record block =
  block_prevBlockHash :: hash
  block_txs :: "transaction list"
(* shall I add blockNumber here? *)

axiomatization GenesisBlock :: block

type_synonym blockchain = "block list"

type_synonym blockForest = "hash \<Rightarrow> block option"

(* txpool: might not be needed *)

axiomatization hashB :: "block \<Rightarrow> hash" ("#")
  where hashB_inj : "inj hashB"

axiomatization sigValidEpoch :: "address \<Rightarrow> validatorIndex \<Rightarrow> epoch \<Rightarrow> signature \<Rightarrow> bool"
axiomatization sigValidEpochs :: "address \<Rightarrow> validatorIndex \<Rightarrow> hash \<Rightarrow> epoch
  \<Rightarrow> epoch \<Rightarrow> signature \<Rightarrow> bool"
  (* the epochs should be a content of the signed messasge, not the "current epoch".
   * Otherwise a validator can deny having sent a message. *)

(* genProof: might not be needed *)

(* VAF: might not be needed *)
(* FCR: might not be needed *)


definition bcLast :: "blockchain \<Rightarrow> block"
  where "bcLast bc = (if bc = [] then GenesisBlock
                      else last bc)"

definition subchain :: "blockchain \<Rightarrow> blockchain \<Rightarrow> bool"
  where "subchain bc1 bc2 = (\<exists> p q. bc2 = p @ bc1 @ q)"

definition bfHasBlock :: "blockForest \<Rightarrow> block \<Rightarrow> bool"
  where "bfHasBlock bf b = (# b \<in> dom bf)"

definition bfHasNotBlock :: "blockForest \<Rightarrow> block \<Rightarrow> bool"
  where "bfHasNotBlock bf b = (\<not> bfHasBlock bf b)"

definition validBlock :: "block \<Rightarrow> bool"
  where "validBlock b \<equiv> block_prevBlockHash b \<noteq> # b"

definition hasInitBlock :: "blockForest \<Rightarrow> bool"
  where "hasInitBlock bf = (bf (# GenesisBlock) = Some GenesisBlock)"

definition validH :: "blockForest \<Rightarrow> bool"
  where "validH bt = (\<forall> h b. bt h = Some b \<longrightarrow> h = # b)"

lemma validH_remove : "validH bt \<Longrightarrow> validH (bt(h := None))"
  by (simp add: validH_def)

(* From Blockforest.v: We only add "fresh blocks" *)
definition bfExtend :: "blockForest \<Rightarrow> block \<Rightarrow> blockForest"
  where "bfExtend bf b = (if bfHasBlock bf b then bf else bf(# b \<mapsto> b ) )"

lemma validH_extend : "validH bt \<Longrightarrow> validH (bfExtend bt b)"
  by(simp add: validH_def bfExtend_def)

lemma bfExtendIB : "validH bt \<Longrightarrow> hasInitBlock bt \<Longrightarrow> hasInitBlock (bfExtend bt b)"
  using bfExtend_def bfHasBlock_def hasInitBlock_def by auto

(* for avoiding loops, blockForest becomes smaller on each iteration. *)
fun compute_chain' :: "blockForest \<Rightarrow> block \<Rightarrow> nat \<Rightarrow> blockchain"
  where "compute_chain' _ _ 0 = []"
  | "compute_chain' bf b (Suc n') =
      (if # b \<in> dom bf then
         (case bf (block_prevBlockHash b) of
           None \<Rightarrow> [b]
         | Some prev \<Rightarrow>
            (compute_chain' (bf(#b := None)) prev n') @ [b]
         )
       else [])"

(* We don't have the guarantee that a blockForest is finite.
   So there might be some infinite chain. *)
(* However, functions don't need to be constructive. *)

definition compute_chain :: "blockForest \<Rightarrow> block \<Rightarrow> blockchain"
  where
"compute_chain bf b =
   (let resultful_ns = {n | n. compute_chain' bf b n \<noteq> []} in
   (if ({} \<noteq> resultful_ns) \<and> (finite resultful_ns) then
      compute_chain' bf b (Max resultful_ns)
    else
      []))"

definition get_block :: "blockForest \<Rightarrow> hash \<Rightarrow> block"
  where
"get_block bf h = (case bf h of 
  None \<Rightarrow> GenesisBlock
| Some b => b)"

definition all_blocks :: "blockForest \<Rightarrow> block set"
  where
"all_blocks bf = { get_block bf h | h. h \<in> (dom bf) }"

definition is_block_in :: "blockForest \<Rightarrow> block \<Rightarrow> bool"
  where
"is_block_in bf b = (\<exists> h. bf h = Some b)"

lemma all_blocksP : "is_block_in bf b = (b \<in> all_blocks bf)"
by (smt all_blocks_def domD domI get_block_def is_block_in_def mem_Collect_eq option.simps(5))

lemma all_blocksP' : "validH bf \<Longrightarrow> (bfHasBlock bf b) = (b \<in> all_blocks bf)"
  apply(auto simp add: bfHasBlock_def all_blocks_def get_block_def validH_def)
  by (metis UNIV_I domI hashB_inj inj_on_def option.simps(5))

fun goodChain :: "blockchain \<Rightarrow> bool" where
  "goodChain [] = False"
| "goodChain (h # _) = (h = GenesisBlock)"

definition allChains :: "blockForest \<Rightarrow> blockchain set"
  where
"allChains bf = { compute_chain bf b | b. b \<in> all_blocks bf}"

(* for now ignoring transaction validity *)
definition goodChains :: "blockForest \<Rightarrow> blockchain set"
  where "goodChains bf = allChains bf \<inter> { c. goodChain c }"

(* Casper states from Casper.v *)

record epochData =
  epoch_target_hash :: hash
  epoch_voted :: "validatorIndex list"
  epoch_curr_dyn_votes :: "epoch \<Rightarrow> wei option"
  epoch_prev_dyn_votes :: "epoch \<Rightarrow> wei option"
  epoch_is_justified :: bool
  epoch_is_finalized :: bool

record validatorData =
  validator_addr :: address
  validator_withdrawal_addr :: address
  validator_deposit :: "epoch \<Rightarrow> wei option"
  validator_start_dynasty :: "dynasty"
  validator_end_dynasty :: "dynasty"

record casperData =
  casper_epochs :: "epoch \<Rightarrow> epochData option"
  casper_validators :: "validatorIndex \<Rightarrow> validatorData option"
  casper_current_dynasty :: dynasty
  casper_current_epoch :: epoch
  casper_expected_target_hash :: hash
  casper_expected_source_epoch :: epoch
  casper_last_justified_epoch :: epoch
  casper_last_finalized_epoch :: epoch
  casper_dynasty_start_epoch :: "dynasty \<Rightarrow> epoch option"
  casper_total_curr_dyn_deposits :: wei
  casper_total_prev_dyn_deposits :: wei
  casper_block_number :: nat
  casper_next_validator_index :: validatorIndex



definition initCasperData :: casperData
  where
"initCasperData = \<lparr>
  casper_epochs = Map.empty,
  casper_validators = Map.empty,
  casper_current_dynasty = 0,
  casper_current_epoch = 0,
  casper_expected_target_hash = # GenesisBlock,
  casper_expected_source_epoch = 0,
  casper_last_justified_epoch = 0,
  casper_last_finalized_epoch = 0,
  casper_dynasty_start_epoch = Map.empty,
  casper_total_curr_dyn_deposits = 0,
  casper_total_prev_dyn_deposits = 0,
  casper_block_number = 0,
  casper_next_validator_index = 0
\<rparr>"

axiomatization casper_epoch_length :: nat
axiomatization casper_default_end_dynasty :: dynasty
axiomatization casper_min_deposit_size :: wei
axiomatization casper_dynasty_logout_delay :: nat
axiomatization casper_withdrawal_delay :: nat

(* Node.v *)



(* The immediate goal is to somehow instantiate the "casper" locale in
   DynamicValidatorSetOneMessage.thy *)

(* member_1 *)
(* member_2 *)
(* hash_parent *)
(* genesis *)
(* vset_fwd *)
(* vset_rear *)
(* vset_chosen *)

end