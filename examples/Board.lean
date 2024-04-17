import Lforge

/-
The following is adapted from cs1710, modeling a game of Tic-Tac-Toe:
https://csci1710.github.io/book/chapters/intro_modeling/intro_modeling_3.html
https://github.com/tnelson/Forge/blob/main/viz-examples/ttt/ttt.frg

TODO: This might not be a valid Forge sig right now.
-/

abstract sig Player {}
one sig X, O, None extends Player {}

sig Board {
  board: func Int -> Int -> Player
}

pred wellFormed[b: Board] {
  all row, col: Int | {
    (row < 0 or row > 2 or col < 0 or col > 2) =>
      b.board[row][col] = None
  }
}

pred Xturn[b: Board] {
  #{row, col: Int | b.board[row][col] = X} =
  #{row, col: Int | b.board[row][col] = O}
}

pred Oturn[b: Board] {
  add[#{row, col: Int | b.board[row][col] = X}, 1] =
  #{row, col: Int | b.board[row][col] = O}
}

pred balanced[b: Board] {
  Oturn[b] or Xturn[b]
}

pred winRow[b: Board, p: Player] {
  p != None
  some row: Int | {
    p != None
    b.board[row][0] = p
    b.board[row][1] = p
    b.board[row][2] = p
  }
}

pred winCol[b: Board, p: Player] {
  p != None
  some col: Int | {
    b.board[0][col] = p
    b.board[1][col] = p
    b.board[2][col] = p
  }
}

pred winner[b: Board, p: Player] {
  p != None
  winRow[b, p]
  or
  winCol[b, p]
  or {
    b.board[0][0] = p
    b.board[1][1] = p
    b.board[2][2] = p
  } or {
    b.board[0][2] = p
    b.board[1][1] = p
    b.board[2][0] = p
  }
}

pred starting[b: Board] {
  all row, col: Int |
    b.board[row][col] = None
}

pred doNothing[pre: Board, post: Board] {
  -- If a player has won, do nothing
  some p: Player | p != None and winner[pre, p]

  all row2: Int, col2: Int |
    post.board[row2][col2] = pre.board[row2][col2]
}

pred move[pre: Board, post: Board, row: Int, col: Int, p: Player] {
    p != None
    pre.board[row][col] = None
    p = X implies Xturn[pre]
    p = O implies Oturn[pre]
    row <= 2 and row >= 0
    col <= 2 and col >= 0
    -- No winner yet
    all p: Player | (p != None) => not winner[pre, p]

    post.board[row][col] = p
    all row2: Int, col2: Int | (row != row2 or col != col2) implies {
        post.board[row2][col2] = pre.board[row2][col2]
    }
}

one sig Game {
  initialState: one Board,
  next: func Board -> Board
}

pred traces {
  starting[Game/*as Game*/.initialState]

  all sprev: Board |
    Game/*as Game*/.next[sprev] != Game/*as Game*/.initialState

  all b: Board | {
    balanced[b]
    some row, col: Int, p: Player | {
      p != None
      move[b, Game/*as Game*/.next[b], row, col, p] or
      doNothing[b, Game/*as Game*/.next[b]]
    }
  }
}
