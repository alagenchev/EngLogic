(* Engineering Logic: Tic-Tac-Toe Project. *)

Require Import Arith.
Require Import Arith.Even.

(*****************************************************************************)
(** Data Definition *)

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

(*****************************************************************************)
(** Function and Properties. *)

(* Function: Define the move function, to place a piece onto the board. *)
Definition move (b: board) (p: piece_location) (s: piece) : board :=
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

(* -------------------- TEST ------------------- *)
(*Compute make_board *)
(* Define the initial board. *)
Definition game_init : list board := cons (make_board blnk blnk blnk blnk blnk blnk blnk blnk blnk) nil.

Definition brd0 := make_board blnk blnk blnk blnk blnk blnk blnk blnk blnk.
Definition brd1 := (move brd0 one x).
Definition brd2 := move brd1 two x.
Definition brd3 := move brd2 three x.
(* --------------------------------------------- *)

(* Function: If X wins on a board. *)
Definition x_wins (b: board) : bool :=
  match (p1 b), (p2 b), (p3 b), (p4 b), (p5 b), (p6 b), (p7 b), (p8 b), (p9 b) with
  (* horizontal matches *)
  | x, x, x, _, _, _, _, _, _ => true
  | _, _, _, x, x, x, _, _, _ => true
  | _, _, _, _, _, _, x, x, x => true
  (* diagonal matches *)
  | x, _, _, _, x, _, _, _, x => true
  | _, _, x, _, x, _, x, _, _ => true
  (* vertical matches *)
  | x, _, _, x, _, _, x, _, _ => true
  | _, x, _, _, x, _, _, x, _ => true
  | _, _, x, _, _, x, _, _, x => true
  (* whatever is left is all false *)
  | _, _, _, _, _, _, _, _, _ => false
  end.

(* Function: If O wins on a board. *)
Definition o_wins (b: board) : bool :=
  match (p1 b), (p2 b), (p3 b), (p4 b), (p5 b), (p6 b), (p7 b), (p8 b), (p9 b) with
  (* horizontal matches *)
  | o, o, o, _, _, _, _, _, _ => true
  | _, _, _, o, o, o, _, _, _ => true
  | _, _, _, _, _, _, o, o, o => true
  (* diagonal matches *)
  | o, _, _, _, o, _, _, _, o => true
  | _, _, o, _, o, _, o, _, _ => true
  (* vertical matches *)
  | o, _, _, o, _, _, o, _, _ => true
  | _, o, _, _, o, _, _, o, _ => true
  | _, _, o, _, _, o, _, _, o => true
  (* whatever is left is all false *)
  | _, _, _, _, _, _, _, _, _  => false
  end.

(* -------------------- TEST ------------------- *)
Theorem x_wins1: (x_wins brd3) = true.
Proof.
auto.
Qed.

Compute x_wins brd3.
(* --------------------------------------------- *)

(* Property: X wins the game. *)
Inductive x_wins_prop : board -> Prop :=
  cc_x_wins_prop: forall b: board, x_wins b = true -> x_wins_prop b.

(* Property: O wins the game. *)
Inductive o_wins_prop : board -> Prop :=
  cc_o_wins_prop: forall b: board, o_wins b = true -> o_wins_prop b.

(* -------------------- TEST ------------------- *)
Theorem x_wins_prop1: x_wins_prop brd3.
Proof.
apply cc_x_wins_prop.
auto.
Qed.
(* --------------------------------------------- *)

(* Function: If a board has a win. *)
Definition isWin (b: board) : bool :=
  if (orb (x_wins b) (o_wins b)) then true else false.

(* Property: If a board has a win. *)
Inductive isWin_prop : board -> Prop :=
  cc_isWin_prop: forall b: board, isWin b = true -> isWin_prop b.

(* Property: If a board doesn't have a win. *)
Inductive isNotWin_prop : board -> Prop :=
  cc_isNotWin_prop: forall b: board, isWin b = false -> isNotWin_prop b.

(* -------------------- TEST ------------------- *)
Theorem weHaveAWin1: isWin_prop brd3.
Proof.
apply cc_isWin_prop.
auto.
Qed.
(* --------------------------------------------- *)

(* Function: If there is a blank position on a board. *)
Definition weHaveBlanksLeft (b: board) : bool :=
  match (p1 b), (p2 b), (p3 b), (p4 b), (p5 b), (p6 b), (p7 b), (p8 b), (p9 b) with
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

(* -------------------- TEST ------------------- *)
Definition fullBoard:= make_board x x x x x x x x x.
Compute weHaveBlanksLeft brd2.
Compute weHaveBlanksLeft brd3.
Compute weHaveBlanksLeft fullBoard.
(* --------------------------------------------- *)

(* Property: If there is a blank position on a board. *)
Inductive weHaveBlanksLeft_prop : board -> Prop :=
  cc_weHaveBlanksLeft_prop: forall b: board, weHaveBlanksLeft b = true -> weHaveBlanksLeft_prop b.

(* Property: If there is no blank position on a board. *)
Inductive weHaveNoBlanksLeft_prop : board -> Prop :=
  cc_weHaveNoBlanksLeft_prop: forall b: board, weHaveBlanksLeft b = false -> weHaveNoBlanksLeft_prop b.

(* -------------------- TEST ------------------- *)
Theorem weHaveBlanksLeft1: weHaveBlanksLeft_prop brd2.
Proof.
apply cc_weHaveBlanksLeft_prop.
auto. Qed.
(* --------------------------------------------- *)

(* Property: If a board is game over. *)
Inductive gameOver_prop : board -> Prop :=
  cc_gameOver_prop: forall b: board, (weHaveNoBlanksLeft_prop b) \/ (isWin_prop b) -> gameOver_prop b. 

(* -------------------- TEST ------------------- *)
Print or.
Theorem GameIsOver1: gameOver_prop brd3.
Proof.
 apply cc_gameOver_prop.
 apply or_intror.
 apply cc_isWin_prop.
 auto.
 Qed.
(* --------------------------------------------- *)

(* Property: If a board is not game over. *)
Inductive gameNotOver_prop : board -> Prop :=
  cc_gameNotOver_prop: forall b: board, (weHaveBlanksLeft_prop b) /\ (isNotWin_prop b) -> gameNotOver_prop b.

(* -------------------- TEST ------------------- *)
Print and.

Theorem GameIsNotOver1: gameNotOver_prop brd2.
Proof.
 apply cc_gameNotOver_prop.
 apply conj.
 apply cc_weHaveBlanksLeft_prop.
 auto.
 apply cc_isNotWin_prop.
 auto.
 Qed.
(* --------------------------------------------- *)

(* Property: If a piece loaction is blank. *)
Definition pieceLocationIsBlank_prop (b: board) (p: piece_location) : Prop :=
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

(* -------------------- TEST ------------------- *)
Theorem p1_blank: pieceLocationIsBlank_prop brd0 one.
Proof.
simpl.
auto.
Qed.
(* --------------------------------------------- *)

(* Function: The restrict version of the move function, which can only do legal moves. *)
Definition restrictedMove (b: board) (p: piece_location) (pl: pieceLocationIsBlank_prop b p) (s: piece) : board :=
  move b p s.

(* -------------------- TEST ------------------- *)
Definition bbb:board := restrictedMove brd0 one p1_blank x.

Theorem p2_blank: pieceLocationIsBlank_prop brd0 two.
Proof.
simpl.
auto.
Qed.

Compute restrictedMove bbb two p2_blank x.
(* --------------------------------------------- *)

(* Property: If current player is in turn. *)
(* We have to enforce that X always goes first. *)
Definition playerHasTurn_prop (bl: list board) (s: piece) : Prop :=
  match s with
  | x => odd (length bl)
  | o => even (length bl)
  | blnk => eq (length bl) 0
  end.

(* Function: Get the last board element from a list of board. *)
Definition getLastBoard (bl: list board) : board :=
  match bl with 
  | nil => brd0
  | cons h t => h
  end.

(* Function: Make a move. *)
(* If: 1. Game is not over; 2. Player has turn; 3. Piece location is blank; Then we can make a move. *)
(* Because pieceLocationIsBlank_prop is given here, we don't need to pass it to move function. *)
Definition makeMove (bl: list board)
                    (s: piece)
                    (pl: piece_location) 
                    (p1: gameNotOver_prop (getLastBoard bl))
                    (p2: playerHasTurn_prop bl s)
                    (p3: pieceLocationIsBlank_prop (getLastBoard bl) pl)
                    : list board := 
  cons (move (getLastBoard bl) pl s) bl.


(* Function: Take turn. *)
Definition takeTurn (g: list board) (s: piece) (validTurn: playerHasTurn_prop g s) : list board :=
  g.

(* -------------------- TEST ------------------- *)
Theorem myTurn_1 : playerHasTurn_prop game_init x.
Proof.
  compute. auto with arith.
Defined.

Example game_1 : list board := takeTurn game_init x myTurn_1.

(* Test the game. *)
Definition Game1_0 : list board := cons brd0 nil.
Compute (getLastBoard Game1_0).

Theorem p1_1: gameNotOver_prop (getLastBoard Game1_0).
Proof.
  apply cc_gameNotOver_prop.
  apply conj.
  apply cc_weHaveBlanksLeft_prop.
  auto.
  apply cc_isNotWin_prop.
  auto.
Defined.

Theorem p2_1: playerHasTurn_prop Game1_0 x.
Proof.
  compute. auto with arith.
Defined.

Theorem p3_1: pieceLocationIsBlank_prop (getLastBoard Game1_0) five.
Proof.
  simpl.
  auto.
Defined.

Definition Game1_1 : list board := makeMove Game1_0 x five p1_1 p2_1 p3_1.
Compute (getLastBoard Game1_1).

(* So here we can see that once we give the proof of three things:
 * 1. game is not over; 2. player has turn; 3. piece location is blank;
 * Then we can make a valid move and create a now board.
 * 
 * The problem is:
 * We have to prove three things before every move.
 * Can we automatically generate the proof?
 *)

(* --------------------------------------------- *)
