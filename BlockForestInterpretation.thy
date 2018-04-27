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
  deposit_withdrawal_addr :: address
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

datatype sender =
  NullSender
| AddrSender address

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

type_synonym validatorMap = "validatorIndex \<Rightarrow> validatorData option"

definition deleteValidator :: "validatorIndex \<Rightarrow> validatorMap \<Rightarrow> validatorMap"
  where "deleteValidator validator_index validators =
            validators(validator_index := None)"

axiomatization updateDeposit :: "validatorMap \<Rightarrow> epoch \<Rightarrow> wei"

record sendAccount =
  send_account_addr :: address
  send_account_wei :: wei

(* XXX do I need to model this sendAccount thing? *)

definition procContractCallTx :: "nat \<Rightarrow> transaction \<Rightarrow> casperData
  \<Rightarrow> casperData * sendAccount list"
  where "procContractCallTx block_number t st =
    (let sender = tx_sender t in
    (let validators = casper_validators st in
    (let epochs = casper_epochs st in
    (let current_epoch = casper_current_epoch st in
    (let current_dynasty = casper_current_dynasty st in
    (let next_validator_index = casper_next_validator_index st in
    (let dynasty_start_epoch = casper_dynasty_start_epoch st in
    (case tx_call t of
        DepositCall d \<Rightarrow>
        (* check non-null sender *)
          (case sender of AddrSender sender_addr \<Rightarrow>
            (let amount = deposit_amount d in
            (let valid_block_epoch =
              (current_epoch = block_number div casper_epoch_length) in
            (let valid_amount = (casper_min_deposit_size <= amount) in
            (if valid_block_epoch \<and> valid_amount then
              (let deposits = [casper_current_dynasty st \<mapsto> amount] in
              (let validation_addr = deposit_validation_addr d in
              (let withdrawal_addr = deposit_withdrawal_addr d in
              (let start_dynasty = casper_current_epoch st + 2 in
              (let validator_data =
                 \<lparr> validator_addr = validation_addr,
                   validator_withdrawal_addr = withdrawal_addr,
                   validator_deposit = deposits,
                   validator_start_dynasty = start_dynasty,
                   validator_end_dynasty = casper_default_end_dynasty \<rparr> in
              (let validators' = [next_validator_index \<mapsto> validator_data] ++ validators in
              (let st'0 = st\<lparr> casper_validators := validators' \<rparr> in
              (let st'1 = st'0\<lparr>casper_next_validator_index := next_validator_index + 1 \<rparr> in
                (st'1, [])))))))))
             else
              (st, [])))))
           | _ \<Rightarrow>
             (st, []))

      | VoteCall v \<Rightarrow>
          (let validator_index = vote_validator_index v in
          (let target_hash = vote_target_hash v in
          (let target_epoch = vote_target_epoch v in
          (let source_epoch = vote_source_epoch v in
          (let sig = vote_sig v in
          (* look up validator *)
          (case validators validator_index of Some validator \<Rightarrow>
            (let validation_addr = validator_addr validator in
            (* look up epoch *)
            (case epochs target_epoch of Some epoch_data \<Rightarrow>
              (let voted = epoch_voted epoch_data in
              (if validator_index \<notin> set voted then
                (let voted' = voted @ [validator_index] in
                (let epoch_data' = epoch_data\<lparr> epoch_voted := voted' \<rparr> in
                (let epochs' = epochs( target_epoch \<mapsto> epoch_data' ) in
                (let st' = st\<lparr> casper_epochs := epochs' \<rparr> in
                (st', [])))))
               else
                 (st, [])))
             | None \<Rightarrow>
               (st, [])))
           | None \<Rightarrow>
             (st, [])))))))

      | LogoutCall l \<Rightarrow>
    (* check non-null sender *)
          (case sender of AddrSender sender_addr \<Rightarrow>
            (let validator_index = logout_validator_index l in
            (let epoch = logout_epoch l in
            (let sig = logout_sig l in
            (* look up validator *)
            (case validators validator_index of Some validator \<Rightarrow>
              (let addr = validator_addr validator in
              (let (end_dynasty :: nat) = current_dynasty + casper_dynasty_logout_delay in
              (let valid_block_epoch = (current_epoch = block_number div casper_epoch_length) in
              (let valid_epoch = (epoch <= current_epoch) in
              (let valid_sig = sigValidEpoch addr validator_index epoch sig in
              (let valid_dynasty = (end_dynasty < validator_end_dynasty validator) in
              (if valid_block_epoch \<and> valid_epoch \<and> valid_sig \<and> valid_dynasty then
                (let validator' = validator\<lparr> validator_end_dynasty := end_dynasty \<rparr> in
                (let validators' = [validator_index \<mapsto> validator'] ++ validators in
                (let st' = st\<lparr> casper_validators := validators' \<rparr> in
                (* TODO: update dynasty_wei_delta *)
                  (st', []))))
               else
                 (st, []))))))))
             | None \<Rightarrow>
               (st, [])))))
           | _ \<Rightarrow>
             (st, []))

  | WithdrawCall validator_index \<Rightarrow>
      (* check non-null sender *)
      (case sender of AddrSender sender_addr \<Rightarrow>
        (* look up validator *)
        (case validators validator_index of Some validator \<Rightarrow>
          (let validator_deposit = validator_deposit validator in
          (let validator_withdrawal_addr = validator_withdrawal_addr validator in
          (let validator_end_dynasty = validator_end_dynasty validator in
          (* look up end epoch of validator *)
          (case dynasty_start_epoch (validator_end_dynasty + 1) of Some end_epoch \<Rightarrow>
            (* look up validator deposit for end epoch *)
            (case validator_deposit end_epoch of Some deposit \<Rightarrow>
              (let valid_dynasty = validator_end_dynasty + 1 \<le> current_dynasty in
              (let valid_epoch = end_epoch + casper_withdrawal_delay \<le> current_epoch in
                (if valid_dynasty \<and> valid_epoch then
                  (* delete validator information *)
                  (let validators' = deleteValidator validator_index validators in
                  (* return deposit *)
                  (let st' = st\<lparr> casper_validators := validators' \<rparr> in
                  (let sa' = [\<lparr> send_account_addr = validator_withdrawal_addr,
                                send_account_wei = deposit \<rparr>] in
                    (st', sa'))))
                 else
                   (st, []))))
             | None \<Rightarrow>
               (st, []))
           | None \<Rightarrow>
             (st, [])))))
         | None \<Rightarrow>
           (st, []))
       | _ \<Rightarrow>
         (st, []))

  | InitializeEpochCall e \<Rightarrow> (st, [])

  | SlashCall (v1, v2) \<Rightarrow>
    (* check non-null sender *)
    (case sender of AddrSender sender_addr \<Rightarrow>
      (let validator_index_1 = vote_validator_index v1 in
      (let validator_index_2 = vote_validator_index v2 in
      (let target_hash_1 = vote_target_hash v1 in
      (let target_hash_2 = vote_target_hash v2 in
      (let target_epoch_1 = vote_target_epoch v1 in
      (let target_epoch_2 = vote_target_epoch v2 in
      (let source_epoch_1 = vote_source_epoch v1 in
      (let source_epoch_2 = vote_source_epoch v2 in
      (let sig_1 = vote_sig v1 in
      (let sig_2 = vote_sig v1 in
      (* look up validator *)
      (case validators validator_index_1 of Some validator \<Rightarrow>
        (let validator_deposit = validator_deposit validator in
        (let validator_addr = validator_addr validator in
        (* look up deposit for validator in current epoch *)
        (case validator_deposit current_epoch of Some deposit \<Rightarrow>
          (let valid_sig_1 = sigValidEpochs validator_addr validator_index_1 target_hash_1 target_epoch_1 source_epoch_1 sig_1 in
          (let valid_sig_2 = sigValidEpochs validator_addr validator_index_2 target_hash_2 target_epoch_2 source_epoch_2 sig_2 in
          (let valid_indexes = (validator_index_1 = validator_index_2) in
          (let valid_hashes_epochs = \<not>((target_hash_1 = target_hash_1) \<and> (target_epoch_1 = target_epoch_2) \<and> (source_epoch_1 = source_epoch_2)) in
          (let epoch_cond_1 = (target_epoch_2 < target_epoch_1 \<and> source_epoch_1 < source_epoch_2) in
          (let epoch_cond_2 = (target_epoch_1 < target_epoch_2 \<and> source_epoch_2 < source_epoch_1) in
          (let valid_targets = ((target_epoch_1 = target_epoch_2) \<or> epoch_cond_1 \<or> epoch_cond_2) in
          (if valid_sig_1 \<and> valid_sig_2 \<and> valid_indexes \<and> valid_hashes_epochs \<and> valid_targets then
            (let validators' = deleteValidator validator_index_1 validators in
            (let st' = st\<lparr>casper_validators := validators'\<rparr> in
            (let sa' = [\<lparr> send_account_addr = sender_addr,
                          send_account_wei = deposit \<rparr>] in (* FIXME: scale factor? *)
              (st', sa'))))
          else
            (st, [])))))))))
        | None \<Rightarrow>
          (st, []))))
      | None \<Rightarrow>
        (st, []))))))))))))
    | _ \<Rightarrow>
      (st, []))))))))))"


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
