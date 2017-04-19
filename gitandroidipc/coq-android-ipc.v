(************************************************************************)
(* This library include Coq definitions of Android inter-component communication,
   intent, intent filter and tests required for intent delivery. The proofs
   of intent delivery and intent broadcasts are carried. *)
(************************************************************************)

 Require Import Arith.
 Require Import Atom.
 Require Import List.

(************************ Basic Definitions *********************************************)

(**Decidable equality on atoms *)

Notation "x == y" :=
  (eq_atom_dec x y) (at level 67) : metatheory_scope.
Open Scope metatheory_scope.

Definition eq_atom (x y : atom) : bool := 
    if (x == y) then true else false.

Notation "x =?= y" :=
  (eq_atom x y) (at level 67) : metatheory_scope.

(**Finds a name in the list.*)
Fixpoint find (n: atom) (nl: list atom) : bool :=
 match nl with
 | nil => false
 | cons h tl => if (h =?= n) then true else find n tl
 end.

(**Boolean and*)
Definition andb (b1 b2: bool) : bool :=
 match b1, b2 with
 | true, _ => b2
 | false, _ => false
 end.

(**Boolean or*)
Definition orb (b1 b2: bool) : bool :=
 match b1, b2 with
 | false, false => false
 | _, _ => true
 end.

Notation "b1 & b2" := (andb b1 b2) (at level 60, right associativity). 

(****************************************************************************************)
(**************************** IPC Formalization *****************************************)
(****************************************************************************************)

(*************************** URI, Intent, Filter ****************************************)

(*Content URI: optional scheme, host, port, and path:*)
Inductive uri: Type :=
 | valid_uri: option atom -> option atom -> option nat -> option atom -> uri.

(**Implicit intent: action, category, data (uri, MIME type)*)
Inductive intent: Type := 
  int: atom -> list atom -> uri -> atom -> intent.

(**Intent filter: contain specification of actions, categories, URI and MIME types.*)
Inductive filter: Type :=
  filt: list atom -> list atom -> list uri -> list atom -> filter.


(*************************** Testing ACTION ********************************************)

(**Finds a match for an intent action in the filter actions.*)
Definition testaction (action : atom) (fil : filter) : bool :=
 match fil with 
 | filt actions _ _ _ => find action actions
 end.

(*************************** Testing CATEGORIES ****************************************)

(**Checks if ALL intent categories exist in the filter.*)
Fixpoint testcategory (intentcats : list atom) (filtercats : list atom ) {struct intentcats} : bool :=
  match intentcats with
  | nil => true
  | cons x l => match (find x l) with
           | false => false
           | true => testcategory l filtercats
           end
  end.

(*************************** Testing URI ************************************************)
(*Compare optional filter URI attribute with an intent URI attribute. *)
Definition cmpoattr (on1 on2: option atom) : bool :=
 match on1, on2 with
 | None, _ => true (*if attribute is NOT specified in filter, test is passed.*)
 | Some n1, Some n2 => (n1 =?= n2)
 | Some n, None => false (*if a filter URI attribute is not listed in intent, test fails*)
 end.

(**Equivality on optional port numbers (listed in filter and intent)*)
Definition beq_nato (on1 on2: option nat) : bool :=
 match on1, on2 with
 | None, _ => true  (*no port is specified in filter*)
 | Some n1, Some n2 => beq_nat n1 n2 (*both specifies ports and equality is test*)
 | Some n, None => false (*no port is specified in the intent*)
 end.

(**"When the URI in an intent is compared to a URI specification in a filter, 
 it's compared only to the parts of the URI included in the filter. For example:
 a) If a scheme is not specified, the host is ignored.
 b) If a host is not specified, the port is ignored.
 c) If both the scheme and host are not specified, the path is ignored.
 d) If a filter specifies only a scheme, all URIs with that scheme match the filter. 
 e) If a filter specifies a scheme and an authority but no path, all URIs with the same  
  scheme and authority pass the filter, regardless of their paths.
 f) If a filter specifies a scheme, an authority, and a path, only URIs with the same 
  scheme, authority, and path pass the filter." *)  
Fixpoint testuri (filuri iuri: uri) : bool :=
 match filuri, iuri with 
 | valid_uri None None None None, _ => true (*no URI in filter, test is passed.*)
 | valid_uri None _ (Some port) (Some path), valid_uri _ _ porto patho =>  
    beq_nato (Some port) porto & cmpoattr (Some path) patho (*a*)
 | valid_uri (Some scheme) None _ (Some path), valid_uri schemeo _ _ patho => 
    cmpoattr (Some scheme) schemeo & cmpoattr (Some path) patho (*b*)
 | valid_uri None None (Some port) _, valid_uri _ _ porto _ => 
    beq_nato (Some port) porto (*c*)  
 | valid_uri (Some scheme) None None None, valid_uri (Some scheme') _ _ _ => scheme =?= scheme' (*d*)
 | valid_uri (Some scheme) (Some host) _ None, valid_uri (Some scheme') (Some host') _ _ => 
    (scheme =?= scheme') & (host =?= host')  (*e*)
 | valid_uri (Some scheme) (Some host) _ (Some path), valid_uri (Some scheme') (Some host') _ (Some path') => 
    (scheme =?= scheme') & (host =?= host') & (path =?= path') (*f*)
 | valid_uri schemeo hosto porto patho, valid_uri schemeo' hosto' porto' patho' =>  (*otherwise case*)
    cmpoattr schemeo schemeo' & cmpoattr hosto hosto' & beq_nato porto porto' & cmpoattr patho patho' 
 end.

(**Example of ambiguity captured
 (*If a host is not specified, the port is ignored.*)
 | valid_uri (Some scheme) None _ patho, valid_uri schemeo' _ _ patho' => 
    cmpoattr (Some scheme) schemeo' & cmpoattr patho patho' 

 Contradicts

 If a filter specifies only a scheme, all URIs with that scheme match the filter.
 | valid_uri (Some scheme) None None None, valid_uri (Some scheme') _ _ _ => namecmp scheme scheme'
*)

(*************************** Testing MIME Type *****************************************)

(**Finds an atom (intent type) match in the list of atoms (filter types). 
  NOTE: If there is no type, one should be inferred, however, this is not formalized.*)
Definition testtype (filtypes: list atom) (itype: atom): bool :=
 match filtypes, itype with
 | nil, _ => true
 | filtypes, it => find it filtypes
 end.

(*************************** Testing DATA *********************************************)

(**"The data test compares both the URI and the MIME type in the intent to a URI and MIME type
 specified in the filter. The rules are as follows:
 a) An intent that contains neither a URI nor a MIME type passes the test only if the 
  filter does not specify any URIs or MIME types.
 b) An intent that contains a URI but no MIME type (neither explicit nor inferable from 
  the URI) passes the test only if its URI matches the filter's URI format and the filter
  likewise does not specify a MIME type.
 c) An intent that contains a MIME type but not a URI passes the test only if the filter 
  lists the same MIME type and does not specify a URI format.
 d) An intent that contains both a URI and a MIME type (either explicit or inferable from
  the URI) passes the MIME type part of the test only if that type matches a type listed 
  in the filter. It passes the URI part of the test either if its URI matches a URI in 
  the filter *****or if it has a content: or file: URI and the filter does not specify a 
  URI****. In other words, a component is presumed to support content: and file: data if 
  its filter lists only a MIME type."*)
Fixpoint testdata (iuri: option uri) (itype: option atom) 
      (filuris: list uri) (filtypes: list atom) : bool :=
 match iuri, itype, filuris, filtypes with
 | None, None, nil, nil => true  (*a*)
 | Some u, None, cons u' ul, nil => orb (testuri u' u) (testdata iuri None ul nil)  (*b*)
 | None, Some it, nil, ftl => testtype ftl it (*c*)
 | Some u, Some it, cons u' ul, ftl => 
    (orb (testuri u' u) (testdata iuri None ul nil)) & (testtype ftl it) (*d*)
 | None, None, cons u' ul, nil => false  
 | None, None, nil, cons t' tl => false
 | None, None, cons u' ul, cons t' tl => true  (*a*)
 | _, _, _, _ => false  (*otherwise cases*)
 end.
 

(*************************** Delivering Intent *****************************************)

(**An intent is accepted only if it passes all the three tests*)
Definition accept (i: intent) (f: filter) : bool := 
 match i, f with
 | int a cl u t, filt fal fcl ful ftl => 
    testaction a (filt fal fcl ful ftl) & 
    testcategory cl fcl & 
    testdata (Some u) (Some t) ful ftl
 end.


(****************************************************************************************)
(**************************** Proof of Delivery *****************************************)
(****************************************************************************************)

(**A component accepts an inent ONLY IF it passes all the three tests.*)
Theorem accept_intent: forall a cl u t fal fcl ful ftl, 
  testaction a (filt fal fcl ful ftl) = true ->
  testcategory cl fcl = true ->
  testdata (Some u) (Some t) ful ftl = true ->
  accept (int a cl u t) (filt fal fcl ful ftl) = true.
Proof.
 intros ???????? TA TC TD.
 unfold accept.
 rewrite TA.
 rewrite TC.
 rewrite TD.
 simpl. auto.
Qed.

(*An application is modeled as a filter.*)
Definition application := filter.

(*Android system is a list of application.*)
Definition system := list application. 

(*An intent is broadcast, if it is accepted by every application in the system*)
Fixpoint broadcast (I: intent) (S: system) : bool :=
  match S with
 | nil => true
 | cons A A' => (accept I A) & broadcast I A'
 end.

Lemma app_nil_left : forall l:list application, l = nil++l.
Proof.
 induction l; simpl in |- *; auto.
Qed.

Lemma broadcast_append: forall l l' a I, 
  broadcast I (l'++(a :: l)) = accept I a & broadcast I (l'++l).
Proof.
 intros.
 induction l'.
  (*CASE: l'=nil*)
  do 2 rewrite <- app_nil_left. 
  auto.
  (*CASE: l'=a0::l'*)
  simpl in *.
  rewrite IHl'.
  destruct (accept I a0);simpl;auto.
  destruct (accept I a);simpl;auto.
Qed.

Theorem broadcast_general: forall I A S,
 broadcast I S = true -> 
 In A S ->
 accept I A = true.
Proof.
 intros ?????.
 apply In_split in H0.
 destruct H0.
 destruct H0.
 rewrite H0 in H. 
 rewrite -> broadcast_append in H.
 unfold andb in *.
 destruct (accept I A).
  (*CASE true*)
  auto.
  (*CASE false*)
  inversion H.
Qed.

(****************** End ******************)