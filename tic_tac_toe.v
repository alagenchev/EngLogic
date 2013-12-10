(* Engineering Logic: Tic-Tac-Toe Project. *)

Require Import Arith.
Require Import Arith.Even.

(* Define the piece on the board. Can be x, o, or blank. *)
Inductive piece : Set :=
  | x
  | o
  | blnk.

(* Define the nine locations on the board. *)
Inductive piece_location : Set :=
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine.

(* Define the tic-tac-toe board, which has nine positions. *)
Record board : Set := make_board {
  p1 : piece;
  p2 : piece;
  p3 : piece;
  p4 : piece;
  p5 : piece;
  p6 : piece;
  p7 : piece;
  p8 : piece;
  p9 : piece
}.


(* Define the move function, to place a piece onto the board. *)
Definition move (b: board) (p: piece_location) (s: piece): board :=
  match p with
  | one   => make_board (   s) (p2 b) (p3 b) (p4 b) (p5 b) (p6 b) (p7 b) (p8 b) (p9 b)
  | two   => make_board (p1 b) (   s) (p3 b) (p4 b) (p5 b) (p6 b) (p7 b) (p8 b) (p9 b)
  | three => make_board (p1 b) (p2 b) (   s) (p4 b) (p5 b) (p6 b) (p7 b) (p8 b) (p9 b)
  | four  => make_board (p1 b) (p2 b) (p3 b) (   s) (p5 b) (p6 b) (p7 b) (p8 b) (p9 b)
  | five  => make_board (p1 b) (p2 b) (p3 b) (p4 b) (   s) (p6 b) (p7 b) (p8 b) (p9 b)
  | six   => make_board (p1 b) (p2 b) (p3 b) (p4 b) (p5 b) (   s) (p7 b) (p8 b) (p9 b)
  | seven => make_board (p1 b) (p2 b) (p3 b) (p4 b) (p5 b) (p6 b) (   s) (p8 b) (p9 b)
  | eight => make_board (p1 b) (p2 b) (p3 b) (p4 b) (p5 b) (p6 b) (p7 b) (   s) (p9 b)
  | nine  => make_board (p1 b) (p2 b) (p3 b) (p4 b) (p5 b) (p6 b) (p7 b) (p8 b) (   s)
  end.

(*Compute make_board *)
(* Define the initial board. *)
Definition game_init : list board := cons (make_board blnk blnk blnk blnk blnk blnk blnk blnk blnk) nil.

Definition brd0 := make_board blnk blnk blnk blnk blnk blnk blnk blnk blnk.
Definition brd1 := (move brd0 one x).
Definition brd2:= move brd1 two x.
Definition brd3:= move brd2 three x.

Definition x_wins (b : board): bool:=
match ( p1 b), ( p2 b), ( p3 b), ( p4 b), ( p5 b), ( p6 b), ( p7 b), ( p8 b), ( p9 b) with
  (*begin horizontal matches*)
  | x, x, x, _, _, _, _, _, _ => true
  | _, _, _, x, x, x, _, _, _ => true
  | _, _, _, _, _, _, x, x, x => true
  (*end horizontal matches*)
  (*begin diagonal matches*)
  | x, _, _, _, x, _, _, _, x => true
  | _, _, x, _, x, _, x, _, _ => true
  
  (*end diagonal matches*)
  (*begin vertical matches*)
  |x, _, _, x, _, _, x, _, _ => true
  |_, x, _, _, x, _, _, x, _ => true
  |_, _, x, _, _, x, _, _, x => true
  (*end vertical matches*)
  (*whatever is left is all false*)
  | _, _, _, _, _, _, _, _, _  => false
  end.

Definition o_wins (b : board): bool:=
match ( p1 b), ( p2 b), ( p3 b), ( p4 b), ( p5 b), ( p6 b), ( p7 b), ( p8 b), ( p9 b) with
  (*begin horizontal matches*)
  | o, o, o, _, _, _, _, _, _ => true
  | _, _, _, o, o, o, _, _, _ => true
  | _, _, _, _, _, _, o, o, o => true
  (*end horizontal matches*)
  (*begin diagonal matches*)
  | o, _, _, _, o, _, _, _, o => true
  | _, _, o, _, o, _, o, _, _ => true
  
  (*end diagonal matches*)
  (*begin vertical matches*)
  |o, _, _, o, _, _, o, _, _ => true
  |_, o, _, _, o, _, _, o, _ => true
  |_, _, o, _, _, o, _, _, o => true
  (*end vertical matches*)
  (*whatever is left is all false*)
  | _, _, _, _, _, _, _, _, _  => false
  end.

Theorem x_wins1: (x_wins brd3) = true.
Proof.
auto.
Qed.

Compute x_wins brd3.

Inductive x_wins_prop: board -> Prop:=
  |cc_x_wins_prop: forall b: board, x_wins b = true -> x_wins_prop b.

Inductive o_wins_prop: board -> Prop:=
  |cc_o_wins_prop: forall b: board, o_wins b = true -> o_wins_prop b.


Theorem x_wins_prop1: x_wins_prop brd3.
Proof.
apply cc_x_wins_prop.
auto.
Qed.

Definition isWin (b:board):bool:=
  if(orb (x_wins b) (o_wins b)) then true else false.

Inductive isWin_prop: board->Prop:=
    |cc_isWin_prop: forall b:board, isWin b = true -> isWin_prop b.
 
Theorem weHaveAWin1: isWin_prop brd3.
Proof.
apply cc_isWin_prop.
auto.
Qed.

Definition weHaveBlanksLeft (b:board): bool :=
  match ( p1 b), ( p2 b), ( p3 b), ( p4 b), ( p5 b), ( p6 b), ( p7 b), ( p8 b), ( p9 b) with
    | blnk, _, _, _, _, _, _, _, _  => true
    | _, blnk, _, _, _, _, _, _, _  => true
    | _, _, blnk, _, _, _, _, _, _  => true
    | _, _, _, blnk, _, _, _, _, _  => true
    | _, _, _, _, blnk, _, _, _, _  => true
    | _, _, _, _, _, blnk, _, _, _  => true
    | _, _, _, _, _, _, blnk, _, _  => true
    | _, _, _, _, _, _, _, blnk, _  => true
    | _, _, _, _, _, _, _, _, blnk  => true
    | _, _, _, _, _, _, _, _, _  => false
   end.
Definition fullBoard:= make_board x x x x x x x x x.
Compute weHaveBlanksLeft brd2.
Compute weHaveBlanksLeft brd3.
Compute weHaveBlanksLeft fullBoard.

Inductive weHaveBlanksLeft_prop: board -> Prop:=
  | cc_weHaveBlanksLeft_prop: forall b:board, weHaveBlanksLeft b = true-> weHaveBlanksLeft_prop b.

Theorem weHaveBlanksLeft1: weHaveBlanksLeft_prop brd2.
Proof.
apply cc_weHaveBlanksLeft_prop.
auto. Qed.

Inductive gameOver_prop: board-> Prop:=
  |cc_gameOver_prop: forall b:board, (not (weHaveBlanksLeft_prop b)) \/ (isWin_prop b) -> gameOver_prop b. 

Print or.
Theorem GameIsOver1: gameOver_prop brd3.
Proof.
 apply cc_gameOver_prop.
 apply or_intror.
 apply cc_isWin_prop.
 auto.
 Qed.

Definition pieceLocationIsBlank (b:board) (p: piece_location) : Prop :=
     match p with
  | one   => (p1 b) = blnk
  | two   => (p2 b) = blnk
  | three => (p3 b) = blnk
  | four  => (p4 b) = blnk
  | five  => (p5 b) = blnk
  | six   => (p6 b) = blnk
  | seven => (p7 b) = blnk
  | eight => (p8 b) = blnk
  | nine  => (p9 b) = blnk
  end.

Theorem p1_blank: pieceLocationIsBlank brd0 one.
Proof.
simpl.
auto.
Qed.

Definition restrictedMove (b: board) (p: piece_location)(pl: pieceLocationIsBlank b p) (s: piece): board :=
move b p s.

Definition bbb:board := restrictedMove brd0 one p1_blank x.

Theorem p2_blank: pieceLocationIsBlank brd0 two.
Proof.
simpl.
auto.
Qed.

Compute restrictedMove bbb two p2_blank x.


(*we have to enforce that x always goes first*)
Definition hasTurn (g : list board) (s : piece) : Prop :=
  match s with
    | x => odd (length g)
    | o => even (length g)
    | blnk => eq (length g) 0
  end.

Definition getLastBoard (bl : list board):board:=
  match bl with 
  | nil => brd0
  | cons h t => h
  end.


Inductive gameNotOver_prop: board-> Prop:=
  |cc_gameNotOver_prop: forall b:board, (weHaveBlanksLeft_prop b) /\ (~isWin_prop b) -> gameNotOver_prop b.

Print and.

Theorem GameIsNotOver1: gameNotOver_prop brd2.
Proof.
 apply cc_gameNotOver_prop.
 apply conj.
 apply cc_weHaveBlanksLeft_prop.
 auto.
 unfold not.
 intros.
 generalize H.
simpl.
 Qed.



Definition makeMove (bl:list board) (s:piece) (validTurn: hasTurn bl s) (pl: piece_location) 
              (plb: pieceLocationIsBlank (getLastBoard bl) pl) (gno: ~gameOver_prop (getLastBoard bl)): list board:= 
           cons (restrictedMove (getLastBoard bl) pl plb s) bl.











(*Starting Mathew's contributions*)

Definition takeTurn (g : list board) (s : piece) (validTurn : hasTurn g s) : list board :=
  g.

Theorem myTurn_1 : hasTurn game_init x.
Proof.
  compute. auto with arith.
Defined.

Example game_1 : list board := takeTurn game_init x myTurn_1.