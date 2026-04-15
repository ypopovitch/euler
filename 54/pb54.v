
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Fixpoint count_a (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest =>
      if Ascii.eqb c "a"%char
      then 1 + count_a rest
      else count_a rest
  end.

  
Inductive Color :=
  | D
  | H
  | S
  | C
  .
  
Inductive Value :=
  | Ac
  | Ki 
  | Qu 
  | Ja
  | Te
  | N9
  | N8
  | N7
  | N6
  | N5
  | N4
  | N3
  | N2
  | N1
  .

Inductive Card :=
    | CardC (v : Value) (c : Color).

Inductive Hand :=
  | SoloHand (cd : Card)
  | MultiHand (cd : Card) (h : Hand).
  
Inductive EqCardVal : Card -> Card -> Prop :=
  | EqCardValSame : forall (v : Value) (c1 c2 : Color), 
  EqCardVal (CardC v c1) (CardC v c2).
  
Definition DiffCardVal (cd1 cd2 : Card) :=
  ~ EqCardVal cd1 cd2.
  
Inductive CardContainsColor : Color -> Card -> Prop :=
  | CardContains : forall (v : Value) (c : Color),
    CardContainsColor c (CardC v c).
    
Inductive HandContainsColor : Color -> Hand -> Prop :=
  | HandContainsColorHead : forall (cd : Card) (h : Hand) (c : Color),
    CardContainsColor c cd ->
    HandContainsColor c (MultiHand cd h)
  | HandContainsColorTail : forall (cd : Card)  (h : Hand) (c : Color),
    HandContainsColor c h ->
    HandContainsColor c (MultiHand cd h).
    
Definition DiffColor (c1 c2 : Color) :=
  forall (h : Hand), HandContainsColor c1 h /\ (~ HandContainsColor c2 h).
  
Fixpoint HandLen (h : Hand) : nat :=
  match h with
  | SoloHand cd => 1
  | MultiHand cd h' => 1 + (HandLen h')
  end.
  
(*
Inductive CardNbVal : Card -> Hand -> nat -> Prop :=
  | CardNbValFound : forall (cd1 cd2 : Card) (h : Hand) (n : nat),
    EqCardVal cd1 cd2 ->
    CardNbVal cd1 (MultiHand cd2 h) n ->
    CardNbVal cd1 h (n+1)
  | CardNbValNotFound : forall (cd1 cd2 : Card) (h : Hand) (n : nat),
    (~ EqCardVal cd1 cd2) ->
    CardNbVal cd1 (MultiHand cd2 h) n ->
    CardNbVal cd1 h n.
*)
    
Definition FiveCardInHand (h : Hand) :=
  HandLen h = 5.
  
(*
Definition AppearNb (cd : Card) (h : Hand) (n : nat) :=
  CardNbVal cd h 0 /\ CardNbVal cd EmptyHand n.
*)

Definition AppearNb (cd : Card) (h : Hand) (n : nat) :=
  match h with
  | SoloHand cd => 1
  | MultiHand cd h => 1 + AppearNb
    
Inductive Game :=
  | GameC (h1 h2 : Hand) (H1 : HandLen h1 = 5) (H2 : HandLen h2 = 5).
      
Inductive GameSuite :=
  | EmptyGame
  | G2 (g : Game) (gs : GameSuite).
  
Inductive IsHigherValue : Card -> Card -> Prop :=
  | KQ : forall (c1 c2 : Color), IsHigherValue (CardC Ki c1) (CardC Qu c2)
  | QV : forall (c1 c2 : Color), IsHigherValue (CardC Qu c1) (CardC Ja c2)
  | Trans : forall (cd1 cd2 cd3: Card),
    IsHigherValue cd1 cd2 -> IsHigherValue cd2 cd3 -> IsHigherValue cd1 cd3.
    
Definition IsDirectAboveVal (cd1 cd2 : Card) :=
  IsHigherValue cd1 cd2 ->
  (~ exists (cd3 : Card), IsHigherValue cd1 cd3 /\ IsHigherValue cd3 cd2).
  
Definition HandContains (h : Hand) (cd : Card) :=
  ~ AppearNb cd h 0.
  
Inductive Combo :=
  | HighCard
  | Pair
  | TwoPairs
  | Triple
  | Straight
  | Flush
  | FullHouse
  | Four
  | StraighFlush
  | RoyalFlush
  .
  
Inductive IsBetterCombo : Combo -> Combo -> Prop :=
  | TwoPairsPairs : IsBetterCombo TwoPairs Pair
  | TripleTwoPairs : IsBetterCombo Triple TwoPairs
  | StraightTriple : IsBetterCombo Straight Triple
  | FlushStraight : IsBetterCombo Flush Straight
  | FullHouseFlush : IsBetterCombo FullHouse Flush
  | FourFullHouse : IsBetterCombo Four FullHouse
  | StraighFlushFour : IsBetterCombo StraighFlush Four
  | RoyalFlushStraighFlush : IsBetterCombo RoyalFlush StraighFlush  
  | Trans2 : forall (cb1 cb2 cb3: Combo), 
    IsBetterCombo cb1 cb2 -> IsBetterCombo cb2 cb3 -> IsBetterCombo cb1 cb3.

Definition combo_rank (c : Combo) : nat :=
  match c with
  | HighCard => 0
  | Pair => 1
  | TwoPairs => 2
  | Triple => 3
  | Straight => 4
  | Flush => 5
  | FullHouse => 6
  | Four => 7
  | StraighFlush => 8
  | RoyalFlush => 9
  end.

Lemma IsBetterCombo_rank : forall c1 c2, IsBetterCombo c1 c2 -> combo_rank c1 > combo_rank c2.
Proof.
  intros c1 c2 H.
  induction H.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
  - simpl; lia.
Qed.

(**
High Card: Highest value card.
One Pair: Two cards of the same value.
Two Pairs: Two different pairs.
Three of a Kind: Three cards of the same value.
Straight: All cards are consecutive values.
Flush: All cards of the same suit.
Full House: Three of a kind and a pair.
Four of a Kind: Four cards of the same value.
Straight Flush: All cards are consecutive values of same suit.
Royal Flush: Ten, Jack, Queen, King, Ace, in same suit.
**)

Definition IsPair (h : Hand) :=
  exists (cd : Card), AppearNb cd h 2.
 
Definition IsTwoPairs (h : Hand) :=
  exists (cd1 cd2 : Card), 
  AppearNb cd1 h 2 -> 
  AppearNb cd1 h 2 ->
  DiffCardVal cd1 cd2.
  
Definition IsTriple (h : Hand) :=
  exists (cd : Card), AppearNb cd h 3.
  
Definition IsStraight (h : Hand) :=
  exists (cd1 cd2 cd3 cd4 cd5 : Card),
  HandContains h cd1 -> HandContains h cd2 -> HandContains h cd3 ->
  HandContains h cd4 -> HandContains h cd5 ->
  IsDirectAboveVal cd1 cd2 -> IsDirectAboveVal cd2 cd3 -> 
  IsDirectAboveVal cd3 cd4 -> IsDirectAboveVal cd4 cd5.
  
Definition IsFlush (h : Hand) :=
  ~ exists (c1 c2 : Color),
  DiffColor c1 c2 /\
  HandContainsColor c1 h /\ 
  HandContainsColor c2 h.
  
Definition IsFullHouse (h : Hand) :=
  exists (cd1 cd2 : Card),
  DiffCardVal cd1 cd2 ->
  AppearNb cd1 h 3 ->
  AppearNb cd2 h 2.
  
Definition IsFour (h : Hand) :=
  exists (cd : Card), AppearNb cd h 4.
  
Definition IsStraighFlush (h : Hand) :=
 IsStraight h /\ IsFlush h.
 
Definition IsRoyalFlush (h : Hand) :=
 IsStraighFlush h /\ HandContains h (CardC Ac H).

Inductive ContainsCombo : Hand -> Combo -> Prop :=
  | ContainsHighCard : forall (cd : Card) (h : Hand), ContainsCombo (H2 cd h) HighCard
  | ContainsPair : forall (h : Hand), IsPair h -> ContainsCombo h Pair
  | ContainsTwoPairs : forall (h : Hand), IsTwoPairs h -> ContainsCombo h TwoPairs
  | ContainsTriple : forall (h : Hand), IsTriple h -> ContainsCombo h Triple
  | ContainsStraight : forall (h : Hand), IsStraight h -> ContainsCombo h Straight
  | ContainsFlush : forall (h : Hand), IsFlush h -> ContainsCombo h Flush
  | ContainsFullHouse : forall (h : Hand), IsFullHouse h -> ContainsCombo h FullHouse
  | ContainsFour : forall (h : Hand), IsFour h -> ContainsCombo h Four
  | ContainsStraighFlush : forall (h : Hand), IsStraighFlush h -> ContainsCombo h StraighFlush
  | ContainsRoyalFlush : forall (h : Hand), IsRoyalFlush h -> ContainsCombo h RoyalFlush.

Definition HighestCombo (h : Hand) (cb : Combo) :=
  ContainsCombo h cb ->
  ~ (exists (cb2 : Combo), ContainsCombo h cb2 /\ IsBetterCombo cb cb2).
  
Definition ContainsCard (h : Hand) (cd : Card) :=
  AppearNb cd h 1.
  
Inductive IsBestCardHigher : Hand -> Hand -> Prop :=
  | BestCardHigher : forall (h1 h2 : Hand),
    (exists (cd1 cd2 : Card),
     ContainsCard h1 cd1 ->
     ContainsCard h2 cd2 ->
     IsHigherValue cd1 cd2) ->
    IsBestCardHigher h1 h2.
    
Definition TieRank (h1 h2 : Hand) :=
  ~ exists (cb1 cb2 : Combo),
  IsBetterCombo cb1 cb2 ->
  HighestCombo h1 cb1 ->
  HighestCombo h2 cb2.

Inductive IsHigherRanked : Hand -> Hand -> Prop :=
  | BetterCombo : forall (h1 h2 : Hand),
    (exists (cb1 cb2 : Combo), 
      IsBetterCombo cb1 cb2 ->
      HighestCombo h1 cb1 ->
      HighestCombo h2 cb2) ->
      IsHigherRanked h1 h2
  | BetterCard : forall (h1 h2 : Hand),
    TieRank h1 h2 ->
    IsBestCardHigher h1 h2 ->
    IsHigherRanked h1 h2.
    
Definition PlayerOneWins (g : Game) :=
  match g with
  | GameC h1 h2 Hy1 Hy2 => IsHigherRanked h1 h2
  end.
  
Definition PlayerOneDontWins (g : Game) :=
  match g with
  | GameC h1 h2 Hy1 Hy2 => ~ IsHigherRanked h1 h2
  end.
  
Inductive GetNbOfPlayerOneWinsStep : GameSuite -> nat -> Prop :=
  | StepPlus : forall (g : Game) (gs : GameSuite),
    PlayerOneWins g ->
    GetNbOfPlayerOneWinsStep (G2 g gs) 0 ->
    GetNbOfPlayerOneWinsStep gs 1
  | StepEqual : forall (g : Game) (gs : GameSuite),
    PlayerOneDontWins g ->
    GetNbOfPlayerOneWinsStep (G2 g gs) 0 ->
    GetNbOfPlayerOneWinsStep gs 0.
    
    
(* Theorems *) 
 
Theorem TripleBeatsPair :
  IsBetterCombo Triple Pair.
Proof. apply Trans2 with TwoPairs. constructor. constructor. Qed.

Theorem FourBeatsPair :
  IsBetterCombo Four Pair.
Proof. apply Trans2 with FullHouse.
  constructor.
  apply Trans2 with Flush.
  constructor.
  apply Trans2 with Straight.
  constructor.
  apply Trans2 with Triple.
  constructor.
  apply TripleBeatsPair.
  Qed.

Check IsBetterCombo_rank.
  
Theorem TripleIsNotBetterThanTwoPairs :
  ~ IsBetterCombo TwoPairs Triple.
Proof.
  intros H.
  apply IsBetterCombo_rank in H.
  simpl in H.
  lia.
Qed.

Theorem RoyalFlushHighestComboBeatsStraight :
  forall (h1 h2 : Hand),
  HighestCombo h1 RoyalFlush ->
  HighestCombo h2 Straight ->
  IsHigherRanked h1 h2.
Proof.
  intros.
  apply BetterCombo. exists RoyalFlush. exists Straight. intros. assumption. Qed.
  
Theorem AllHandContainsCombo :
  forall (h : Hand), exists (cb : Combo), ContainsCombo h cb.
Proof.
  intros. destruct h.
  
Theorem AllHandContainsHighestCombo :
  forall (h : Hand), exists (cb : Combo), HighestCombo h cb.
Proof.
  intros. destruct h.
  -
  
  

Theorem RoyalFlushHighestComboBeatsAll :
  forall (h1 h2 : Hand) (cb : Combo),
  HighestCombo h1 RoyalFlush ->
  ~ HighestCombo h2 RoyalFlush ->
  IsHigherRanked h1 h2.
Proof.
  intros. apply BetterCombo. exists RoyalFlush.
  pose proof (AllHandContainsHighestCombo h2).
  destruct H3. exists x. intros. assumption. Qed.