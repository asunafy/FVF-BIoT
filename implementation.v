Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Arith.


Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.



Definition address : Type := nat.
Definition time : Type := nat.
Inductive uid : Type :=
  | UID (device fog msg_sender: address)(block_timestamp: time).


Definition DefAdmArr : list address := nil. 
Record Token : Type :=
{ UID_t: uid;
user_t: address;
dev_t: address;
fog_t: address; }.

Record Devices : Type :=
{ dev_d: address;
fog_d: address; }.

Inductive Event : Type :=
| AdminAdded (newAdmin msg_sender: address)
| UserDeviceMappingAdded (user device msg_sender fog: address)
| DeviceDoesnotExist (device fog msg_sender: address)
| FogDeviceMapping (fog device msg_sender: address)
| AdminDeleted (admin msg_sender: address)
| UserDeviceAllMappingDeleted (user msg_sender: address)
| FogDeviceAllMappingDeleted (fog msg_sender: address)
| NotAuthenticated (msg_sender: address)
| Authenticated (msg_sender dev fog: address)
| TokenCreated (UID: uid) (msg_sender dev fog: address)
| DefEv.


Definition DefTkArr : list Token := nil.

Definition DefDevArr : list Devices := nil.

Definition DefEvArr : list Event := nil.

Definition total_map (A : Type) := address -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition eqb_ad (n m: address): bool :=
  if n=?m then true else false.

Fixpoint eqb n m : bool :=
  match n, m with
    | 0, 0 => true
    | 0, S _ => false
    | S _, 0 => false
    | S n', S m' => eqb n' m'
  end.

Lemma eqb_reflx : forall n, eqb n n = true.
Proof.
  intros. unfold eqb. induction n as [| n'0 IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) rewrite -> IHn'. reflexivity. Qed.

Definition t_update {A : Type} (m : total_map A)
                    (x : address) (v : A) :=
  fun x' => if eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Definition DefAddress : address := 0.


Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Notation "x '!->' v" := (t_update (t_empty DefAdmArr) x v) (at level 100).

Notation "x '|->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (t_update (t_empty DefDevArr) x v) (at level 100).

Theorem eqb_address_refl : forall s : address, true = eqb s s.
Proof.
  intros s. unfold eqb. 
   induction s as [| s'].
  - reflexivity.
  - rewrite <- IHs'. reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update.  rewrite <- eqb_address_refl.
  reflexivity.
Qed.


Definition TestAdmArr := DefAdmArr ++ [20].

Definition TestDev := DefDevArr ++ [ (Build_Devices 66 77) ]. 

Record State : Type :=
{ admins: list address; 
  Tokens: list Token;
  events: list Event;
  fog_devices: total_map (list address);
  users_devices: total_map (list Devices);
  msg_sender: address;
  block_timestamp: time;
  last_fun_suc: bool
}.

Inductive Function : Type :=
  | addAdmin (newAdmin: address)
  | addUserDeviceMapping (user device fog: address)
  | addDeviceFogMapping (device fog: address)
  | delAdmin (admin: address)
  | delUser (user: address)
  | delDev (fog: address)
  | requestAuthentication (device fog: address)
  | Seq (f1 f2 : Function).

Fixpoint in_al (l: list address) (e: address) : bool :=
  match l with
  | nil => false
  | h :: t => if eqb h e then true else in_al t e
  end.
  
Fixpoint in_dl_d (l: list Devices) (dev: address) : bool :=
  match l with
  | nil => false
  | h :: t => if eqb h.(dev_d) dev then true else in_dl_d t dev
  end.
  

Notation "'ADDA(' a ')'" :=
  (addAdmin a) (at level 80, right associativity).
Notation "'ADDUDM(' a ',' b ',' c ')'" :=
  (addUserDeviceMapping a b c) (at level 80, right associativity).
Notation "'ADDDFM(' a ',' b ')'" :=
  (addDeviceFogMapping a b) (at level 80, right associativity).
Notation "'DELA(' a ')'" :=
  (delAdmin a) (at level 80, right associativity).
Notation "'DELU(' a ')'" :=
  (delUser a) (at level 80, right associativity).
Notation "'DELD(' a ')'" :=
  (delDev a) (at level 80, right associativity).
Notation "'REQAUT(' a ',' b ')'" :=
  (requestAuthentication a b) (at level 80, right associativity).
Notation "f1 ;; f2" :=
  (Seq f1 f2) (at level 80, right associativity).

  Fixpoint remove_ad (x : address) (l : list address) : list address :=
    match l with
      | [] => []
      | y::tl => if (eqb x y) then remove_ad x tl else y::(remove_ad x tl)
    end.


Lemma remove_ad_length_le : forall l x, length (remove_ad x l) <= length l.
  Proof.
    intro l; induction l as [|y l IHl]; simpl; intros x; trivial.
    destruct (eqb x y); simpl.
    + rewrite IHl; constructor; reflexivity.
    + apply (proj1 (Nat.succ_le_mono _ _) (IHl x)).
  Qed.

Reserved Notation "st '=[' f ']=>' st'"
                  (at level 40).
Inductive Step : Function -> State -> State -> Prop :=
  | E_add_Admin : forall st st' newAdmin,
      in_al st.(admins) st.(msg_sender) = true -> 
      st'.(admins) =  [newAdmin] ++ st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [AdminAdded newAdmin st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = true ->
      st =[ ADDA(newAdmin) ]=> st'
  | E_add_UserDeviceMapping_exist : forall st st' user dev fog, 
      in_al st.(admins) st.(msg_sender) = true -> 
      in_al (st.(fog_devices) fog) dev = true -> 
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [UserDeviceMappingAdded user dev st.(msg_sender) fog] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = (user |-> [Build_Devices dev fog] ++ st.(users_devices) user; st.(users_devices)) ->
      st'.(last_fun_suc) = true ->
      st =[ ADDUDM(user, dev, fog)]=> st'
  | E_add_UserDeviceMapping_not_exist : forall st st' user dev fog, 
      in_al st.(admins) st.(msg_sender) = true -> 
      in_al (st.(fog_devices) fog) dev = false -> 
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [DeviceDoesnotExist dev fog st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = false ->
      st =[ ADDUDM(user, dev, fog) ]=> st'
  | E_add_DeviceFogMapping : forall st st' dev fog, 
      in_al st.(admins) st.(msg_sender) = true ->      
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [FogDeviceMapping fog dev st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = (fog |-> [dev] ++ st.(fog_devices) fog; st.(fog_devices)) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = true ->
      st =[ ADDDFM(dev, fog) ]=> st'
  | E_del_Admin : forall st st' admin, 
      in_al st.(admins) st.(msg_sender) = true -> 
      2 <=? (length st.(admins)) = true ->
      st'.(admins) = (remove_ad admin (st.(admins))) ->
      1 <=? (length st'.(admins)) = true ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [AdminDeleted admin st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = true ->
      st =[ DELA(admin) ]=> st'
  | E_del_Admin_fail : forall st st' admin, 
      in_al st.(admins) st.(msg_sender) = true -> 
      2 <=? (length st.(admins)) = false ->
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = false ->
      st =[ DELA(admin) ]=> st'
  | E_del_User : forall st st' user, 
      in_al st.(admins) st.(msg_sender) = true -> 
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [UserDeviceAllMappingDeleted user st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = (user |-> nil; st.(users_devices)) ->
      st'.(last_fun_suc) = true ->
      st =[ DELU(user) ]=> st'
  | E_del_Dev : forall st st' fog, 
      in_al st.(admins) st.(msg_sender) = true -> 
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [FogDeviceAllMappingDeleted fog st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = (fog |-> nil; st.(fog_devices)) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = true ->
      st =[ DELD(fog) ]=> st'
  | E_req_Auth_not_1 : forall st st' dev fog, 
      in_al (st.(fog_devices) fog) dev = false -> 
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = st.(Tokens) ->
      st'.(events) = [DeviceDoesnotExist dev fog st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = false ->
      st =[ REQAUT(dev, fog) ]=> st'
  | E_req_Auth_not_2 : forall st st' dev fog, 
      in_al (st.(fog_devices) fog) dev = true -> 
      in_dl_d (st.(users_devices) st.(msg_sender)) dev = false ->
      st'.(admins) = st.(admins) ->
      st'.(events) = [NotAuthenticated st.(msg_sender)] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = false ->
      st =[ REQAUT(dev, fog) ]=> st'
  | E_req_Auth : forall st st' dev fog, 
      in_al (st.(fog_devices) fog) dev = true -> 
      in_dl_d (st.(users_devices) st.(msg_sender)) dev = true ->
      st'.(admins) = st.(admins) ->
      st'.(Tokens) = [Build_Token (UID dev fog st.(msg_sender) st.(block_timestamp)) st.(msg_sender) dev fog] ++ st.(Tokens) ->
      st'.(events) = [TokenCreated (UID dev fog st.(msg_sender) st.(block_timestamp)) st.(msg_sender) dev fog;Authenticated st.(msg_sender) dev fog] ++ st.(events) ->
      st'.(fog_devices) = st.(fog_devices) ->
      st'.(users_devices) = st.(users_devices) ->
      st'.(last_fun_suc) = true ->
      st =[ REQAUT(dev, fog) ]=> st'
  | E_Seq : forall f1 f2 st st' st'',
      st =[ f1 ]=> st' ->
      st' =[ f2 ]=> st'' ->
      st =[ f1 ;; f2 ]=> st''

where "st =[ f ]=> st'" := (Step f st st').

Definition st_1 : State := Build_State [15;1] nil [UserDeviceMappingAdded 15 12 1 16]
                           (16 !-> [12]) (15 |-> [{| dev_d := 12; fog_d := 16 |}])15 88 true.  
Definition st_2: State := Build_State [15;1] [{| UID_t := (UID 12 16 15 88);
                           user_t := 15; dev_t := 12; fog_t := 16 |}] 
                           [TokenCreated (UID 12 16 15 88) 15 12 16;
                           Authenticated 15 12 16;UserDeviceMappingAdded 15 12 1 16] 
                           (16 !-> [12]) (15 |-> [{| dev_d := 12; fog_d := 16 |}]) 15 88 true. 

Example example_req :
  st_1 =[ REQAUT(12, 16) ]=> st_2.
Proof.
  apply E_req_Auth;reflexivity.
Qed.


Definition st_3 : State := Build_State [22;1] nil [AdminAdded 22 1] 
                           (t_empty DefAdmArr) (t_empty DefDevArr) 1 88 true.  
Definition st_4 : State := Build_State [22;1] nil [FogDeviceMapping 16 12 1;
                           AdminAdded 22 1] (16 !-> [12]) (t_empty DefDevArr) 1 88 true. 
Definition st_5 : State := Build_State [22;1] nil [FogDeviceAllMappingDeleted 16 1;
                            FogDeviceMapping 16 12 1;AdminAdded 22 1] 
                            (16 !-> nil;16 !-> [12]) (t_empty DefDevArr) 1 88 true. 

Example example_seq :
  st_3 =[ ADDDFM(12, 16);; DELD(16) ]=> st_5.
Proof.
  apply E_Seq with (st_4). 
  apply E_add_DeviceFogMapping;reflexivity.
  apply E_del_Dev;reflexivity.
Qed.

Theorem eqb_true : forall n : address,
  eqb n n = true.
Proof.
 unfold eqb. induction n as [|n' IHn']. 
  - simpl. reflexivity.  
  - apply IHn'.
Qed.

Fixpoint in_dl_d_f (l: list Devices) (dev fog: address) : bool :=
  match l with
  | nil => false
  | h :: t => if andb (eqb h.(dev_d) dev) (eqb h.(fog_d) fog) then true else in_dl_d_f t dev fog
  end.

Axiom Fog_devices_add : forall st st' dev fog, 
     st =[ ADDDFM(dev, fog) ]=> st' ->
     st'.(last_fun_suc) = true -> 
     st'.(fog_devices) = (fog |-> [dev] ++ st.(fog_devices) fog; st.(fog_devices)).


Theorem Device_fog_mapping_suc : forall st st' dev fog,
  st =[ ADDDFM(dev, fog) ]=> st' ->
  st'.(last_fun_suc) = true -> 
  in_al (st'.(fog_devices) fog) dev = true.
Proof. 
  intros. apply Fog_devices_add in H. 
  + rewrite H; unfold in_al; simpl. 
  unfold t_update. 
  assert (HM1 : eqb fog fog = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM2 : eqb dev dev = true).
  { rewrite eqb_reflx. reflexivity. }
  rewrite HM1,HM2.
  reflexivity.
 + assumption. 
Qed.

Axiom User_device_add : forall st st' dev fog user, 
     st =[ ADDUDM(user, dev, fog) ]=> st' ->
     st'.(last_fun_suc) = true -> 
     st'.(users_devices) = (user |-> [Build_Devices dev fog] ++ st.(users_devices) user; st.(users_devices)).

Theorem User_device_mapping_suc : forall st st' dev fog user,
  st =[ ADDUDM(user, dev, fog) ]=> st' ->
  st'.(last_fun_suc) = true -> 
  in_dl_d_f (st'.(users_devices) user) dev fog = true.
Proof.
  intros. apply User_device_add in H. 
  + rewrite H; unfold in_dl_d_f; simpl. 
  unfold t_update.  
  assert (HM1 : eqb user user = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM2 : (dev_d {| dev_d := dev; fog_d := fog |}) = dev).
  { reflexivity. }
  assert (HM3 : (fog_d {| dev_d := dev; fog_d := fog |}) = fog).
  { reflexivity. }
  assert (HM4 : eqb dev dev = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM5 : eqb fog fog = true).
  { rewrite eqb_reflx. reflexivity. }
  rewrite HM1,HM2,HM3,HM4,HM5.
  reflexivity.
 + assumption. 
Qed. 

Definition eqb_uid (u1 u2: uid): bool :=
  match u1 with
   | UID dev1 fog1 msg_sender1 block_timestamp1 => match u2 with
     | UID dev2 fog2 msg_sender2 block_timestamp2 => 
        andb (andb (eqb dev1 dev2) 
             (eqb fog1 fog2))  
        (andb (eqb msg_sender1 msg_sender2) 
             (eqb block_timestamp1 block_timestamp2))
      end
  end. 

Definition eqb_t (t1 t2: Token) := 
  if ( andb (andb (eqb_uid t1.(UID_t) t2.(UID_t)) 
             (eqb t1.(user_t) t2.(user_t)))  
        (andb (eqb t1.(dev_t) t2.(dev_t)) 
             (eqb t1.(fog_t) t2.(fog_t))))then true else false. 

Fixpoint in_tl (l: list Token) (token: Token) : bool :=
  match l with
  | nil => false
  | h :: t => if (eqb_t h token) then true else in_tl t token
  end.

Axiom Token_add : forall st st' dev fog, 
     st =[ REQAUT(dev, fog) ]=> st' ->
     st'.(last_fun_suc) = true -> 
     st'.(Tokens) = [Build_Token (UID dev fog st.(msg_sender) 
         st.(block_timestamp)) st.(msg_sender) dev fog] ++ st.(Tokens).

Lemma eqb_uid_reflx : forall n, eqb_uid n n = true.
Proof.
  intros. unfold eqb_uid. destruct n eqn:E. 
  assert (HM1 : eqb device device = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM2 : eqb fog fog = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM3 : eqb msg_sender0 msg_sender0 = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM4 : eqb block_timestamp0 block_timestamp0 = true).
  { rewrite eqb_reflx. reflexivity. }
  rewrite HM1,HM2,HM3,HM4.
  reflexivity.
Qed.


Lemma eqb_t_reflx : forall a b c d, 
     (eqb_t  {|  UID_t := a; user_t := b; dev_t := c; fog_t := d |}
      {|  UID_t := a; user_t := b; dev_t := c; fog_t := d |}) = true.
Proof.
  intros. unfold eqb_t. 
  assert (HM1 : (UID_t {| UID_t := a; user_t := b; dev_t := c; fog_t := d |}) = a).
  { reflexivity. }
  assert (HM2 : (user_t {| UID_t := a; user_t := b; dev_t := c; fog_t := d |}) = b).
  { reflexivity. }
  assert (HM3 : (dev_t {| UID_t := a; user_t := b; dev_t := c; fog_t := d |}) = c).
  { reflexivity. }
  assert (HM4 : (fog_t {| UID_t := a; user_t := b; dev_t := c; fog_t := d |}) = d).
  { reflexivity. }
  rewrite HM1,HM2,HM3,HM4. 
  assert (HM5 : eqb_uid a a = true).
  { rewrite eqb_uid_reflx. reflexivity. }
  assert (HM6 : eqb b b = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM7 : eqb c c = true).
  { rewrite eqb_reflx. reflexivity. }
  assert (HM8 : eqb d d = true).
  { rewrite eqb_reflx. reflexivity. }
  rewrite HM5,HM6,HM7,HM8; reflexivity.
Qed.


Theorem Request_Auth_suc : forall st st' dev fog,
st =[ REQAUT(dev, fog) ]=> st' ->
st'.(last_fun_suc) = true ->
in_tl st'.(Tokens) (Build_Token (UID dev fog st.(msg_sender) st.(block_timestamp)) st.(msg_sender) dev fog) = true.
Proof.
  intros. 
  apply Token_add in H. 
  + rewrite H; unfold in_tl; simpl. 
  unfold t_update. 
  assert (HM1 : (eqb_t
    {| UID_t := UID dev fog (msg_sender st) (block_timestamp st);
      user_t := msg_sender st;
      dev_t := dev;
      fog_t := fog |}
    {| UID_t := UID dev fog (msg_sender st) (block_timestamp st);
      user_t := msg_sender st;
      dev_t := dev;
      fog_t := fog |}) = true).
  { apply eqb_t_reflx. }
  rewrite HM1; reflexivity.
 + assumption. 
Qed. 

Axiom Has_Auth : forall st st' dev fog,
      in_al (st.(fog_devices) fog) dev = true -> 
      in_dl_d (st.(users_devices) st.(msg_sender)) dev = true ->
      st =[ REQAUT(dev, fog) ]=> st' ->
      st'.(last_fun_suc) = true.

Theorem Has_Auth_Request_Auth_suc : forall st st' dev fog,
      in_al (st.(fog_devices) fog) dev = true -> 
      in_dl_d (st.(users_devices) st.(msg_sender)) dev = true ->
      st =[ REQAUT(dev, fog) ]=> st' ->
      in_tl st'.(Tokens) (Build_Token (UID dev fog st.(msg_sender) st.(block_timestamp)) st.(msg_sender) dev fog) = true.
Proof.
  intros. apply Request_Auth_suc.
  - assumption.
  - apply (@Has_Auth st st' dev fog); assumption.  
Qed.

Axiom Admin_del : forall st st' admin, 
     st =[ DELA(admin) ]=> st' ->
     st'.(last_fun_suc) = true -> 
      (st'.(admins) = remove_ad admin st.(admins)) /\
     (1 <=? (length st'.(admins)) = true).


Theorem Del_Admin_suc : forall st st' admin,
      st =[ DELA(admin) ]=> st' ->
      st'.(last_fun_suc) = true ->
      length st'.(admins) <= length st.(admins).
Proof. 
   intros. apply Admin_del in H. 
  + destruct H; rewrite H; apply remove_ad_length_le. 
  + assumption.
Qed.

Theorem Admin_num_safe: forall st st' admin,
      st =[ DELA(admin) ]=> st' ->
      st'.(last_fun_suc) = true ->
      1 <=? (length st'.(admins)) = true.
Proof. 
   intros. apply Admin_del in H. 
  + destruct H; rewrite H1; reflexivity. 
  + assumption.
Qed.



































