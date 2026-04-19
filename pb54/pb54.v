
Require Import Stdlib.Strings.String.
Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.

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
    
Definition FiveCardInHand (h : Hand) :=
  HandLen h = 5.

Definition CardVal (cd : Card) :=
  match cd with
  | CardC v c => v
  end.

Definition CardColor (cd : Card) :=
  match cd with
  | CardC v c => c
  end.

Definition EqCardValb (cd1 cd2 : Card) : bool :=
  match CardC (CardVal cd1) (CardColor cd1) with
  | CardC Ac _ => match CardC (CardVal cd2) (CardColor cd2) with | CardC Ac _ => true | _ => false end
  | CardC Ki _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC Ki _ => true | _ => false end
  | CardC Qu _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC Qu _ => true | _ => false end
  | CardC Ja _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC Ja _ => true | _ => false end
  | CardC Te _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC Te _ => true | _ => false end
  | CardC N9 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N9 _ => true | _ => false end
  | CardC N8 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N8 _ => true | _ => false end
  | CardC N7 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N7 _ => true | _ => false end
  | CardC N6 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N6 _ => true | _ => false end
  | CardC N5 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N5 _ => true | _ => false end
  | CardC N4 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N4 _ => true | _ => false end
  | CardC N3 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N3 _ => true | _ => false end
  | CardC N2 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N2 _ => true | _ => false end
  | CardC N1 _ => match CardC (CardVal cd2) (CardColor cd2)  with | CardC N1 _ => true | _ => false end
  end.
  
Fixpoint AppearNb (cd : Card) (h : Hand) : nat :=
  match h with
  | SoloHand cd' => match EqCardValb cd cd' with
                    | true => 1
                    | false => 0
                    end
  | MultiHand cd' h' => match EqCardValb cd cd' with
                        | true => 1 + AppearNb cd h'
                        | false => 0 + AppearNb cd h'
                        end
  end.
    
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
  AppearNb cd h > 0.
  
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
Inductive IsBetterCombo : Combo -> Combo -> Prop :=
  | PairHighCard : IsBetterCombo Pair HighCard
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

Inductive EqCombo : Combo -> Combo -> Prop :=
  | EqComboC : forall (cb : Combo), EqCombo cb cb.

Inductive DirectlyAboveCombo : Combo -> Combo -> Prop :=
  | DirectlyAboveComboC : forall (cb1 cb2 : Combo),
    IsBetterCombo cb1 cb2 ->
    (~ exists (cb3 : Combo), (IsBetterCombo cb1 cb3 /\ 
      IsBetterCombo cb3 cb2)) ->
    DirectlyAboveCombo cb1 cb2.

Inductive DirectlyBelowCombo : Combo -> Combo -> Prop :=
  | DirectlyBelowComboC : forall (cb1 cb2 : Combo),
    IsBetterCombo cb1 cb2 ->
    (~ exists (cb3 : Combo), (IsBetterCombo cb1 cb3 /\ 
      IsBetterCombo cb3 cb2)) ->
    DirectlyBelowCombo cb2 cb1.

Definition IsPair (h : Hand) :=
  exists (cd : Card), AppearNb cd h  = 2.
 
Definition IsTwoPairs (h : Hand) :=
  exists (cd1 cd2 : Card), 
  AppearNb cd1 h = 2 -> 
  AppearNb cd1 h = 2 ->
  DiffCardVal cd1 cd2.
  
Definition IsTriple (h : Hand) :=
  exists (cd : Card), AppearNb cd h = 3.
  
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
  AppearNb cd1 h = 3 ->
  AppearNb cd2 h = 2.
  
Definition IsFour (h : Hand) :=
  exists (cd : Card), AppearNb cd h = 4.
  
Definition IsStraighFlush (h : Hand) :=
 IsStraight h /\ IsFlush h.
 
Definition IsRoyalFlush (h : Hand) :=
 IsStraighFlush h /\ HandContains h (CardC Ac H).

Inductive ContainsCombo : Hand -> Combo -> Prop :=
  | ContainsHighCard : forall (h : Hand), ContainsCombo h HighCard
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
  AppearNb cd h = 1.
  
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

Definition ValRank (v : Value) :=
  match v with
  | Ac => 14
  | Ki => 13
  | Qu => 12
  | Ja => 11
  | Te => 10
  | N9 => 9
  | N8 => 8
  | N7 => 7
  | N6 => 6
  | N5 => 5
  | N4 => 4
  | N3 => 3
  | N2 => 2
  | N1 => 1
  end.

Definition CardRank (cd : Card) :=
  match cd with
  | CardC val _ => ValRank val
  end.


(* TODO 
Fixpoint HandRank (h : Hand) := 0
highest combo rank * (card nb + 1) + highest card rank
*)
    
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

