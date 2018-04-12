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

type_synonym blockForest = "hash \<Rightarrow> block"

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

(* The immediate goal is to somehow instantiate the "casper" locale in
   DynamicValidatorSetOneMessage.thy *)

end