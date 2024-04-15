import Lforge
#lang forge

sig Player {}
-- one sig X extends Player {}
-- one sig O extends Player {}
noncomputable opaque X : Player
noncomputable opaque O : Player

sig Board {
  board: set Int -> Int -> Player
}

pred wellformed[b: Board] {
  all row, col: Int | {
    (row < 0 or row > 2 or col < 0 or col > 2) implies
    no b.board[row][col]
  }
}

pred Xturn[b: Board] {
  -- same number of X and O on board
  #{row, col: Int | b.board[row][col] = X} =
  #{row, col: Int | b.board[row][col] = O}
}

pred Oturn[b: Board] {
  #{row, col: Int | b.board[row][col] = X} =
  add[#{row, col: Int | b.board[row][col] = O}, 1]
}

pred balanced[b: Board] {
  Oturn[b] or Xturn[b]
}

pred winRow[b: Board, p: Player] {
  some row: Int | {
    b.board[row][0] = p and
    b.board[row][1] = p and
    b.board[row][2] = p
  }
}

pred winCol[b: Board, p: Player] {
  some col: Int | {
    b.board[0][col] = p and
    b.board[1][col] = p and
    b.board[2][col] = p
  }
}

pred winner[b: Board, p: Player] {
  winRow[b, p]
  or
  winCol[b, p]
  or {
    b.board[0][0] = p and
    b.board[1][1] = p and
    b.board[2][2] = p
  } or {
    b.board[0][2] = p and
    b.board[1][1] = p and
    b.board[2][0] = p
  }
}

pred starting[b: Board] {
  all row, col: Int |
    no b.board[row][col]
}

pred move[pre: Board, post: Board, row: Int, col: Int, p: Player] {
  -- GUARD (what needs to hold about the pre-state?)
  no pre.board[row][col] -- no move already there
  p = X implies Xturn[pre] -- appropriate turn
  p = O implies Oturn[pre]
  -- What else might we want to add here?

  -- ACTION (what does the post-state then look like?)
  post.board[row][col] = p
  all row2: Int, col2: Int | (row != row2 or col != col2) implies {
    post.board[row2][col2] = pre.board[row2][col2]
  }
}

one sig Game {
  initialState: one Board,
  next: pfunc Board -> Board
}
