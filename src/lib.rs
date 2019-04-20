//! Tree-searching _Sudoku_ solver using forward checking. 🎲
//!
//! # Example
//! ```
//! # use sudoku::sudoku;
//! let mut sudoku = sudoku! [
//!     _ 6 4 2 _ _ 9 3 _
//!     _ _ _ 6 _ _ _ _ _
//!     _ 3 _ 7 _ _ _ 1 _
//!     _ _ _ _ _ _ 6 7 2
//!     _ _ _ _ 1 _ _ _ _
//!     8 9 2 _ _ _ _ _ _
//!     _ 5 _ _ _ 4 _ 9 _
//!     _ _ _ _ _ 8 _ _ _
//!     _ 1 9 _ _ 7 3 4 _
//! ];
//!
//! let solution = sudoku.solve().unwrap();
//! println!("{}", solution);
//! ```

use std::fmt::{self, Display, Debug, Formatter};
use std::collections::HashSet;
use std::ops::Index;


/// A sudoku problem.
#[derive(Clone)]
pub struct Sudoku {
    given: Vec<(u8, u8, u8)>,
    possible: [FieldSet; 81],
    board: [u8; 81],
    friends: Vec<HashSet<u8>>,
}

impl Sudoku {
    /// Create a new sudoku from a board. Missing numbers are denoted by zero.
    #[inline]
    pub fn from_board(board: &[u8; 81]) -> Result<Sudoku, CreationError> {
        Sudoku::from_board_slice(&board[..])
    }

    /// Create a new sudoku from a board slice, which shall have exactly 81 entries.
    /// Missing numbers are denoted by zero.
    #[inline]
    pub fn from_board_slice(board: &[u8]) -> Result<Sudoku, CreationError> {
        let given = board.iter().enumerate().filter_map(|(idx, field)| {
            if *field >= 1 && *field <= 9 {
                Some((idx % 9, idx / 9, *field))
            } else {
                None
            }
        });
        Sudoku::from_given(given)
    }

    /// Create a new sudoku from an iterator of given numbers.
    ///
    /// The items are three-tuples like `(x, y, number)`. Here x denotes
    /// the column and y the row starting at zero.
    pub fn from_given<I>(given: I) -> Result<Sudoku, CreationError>
    where I: IntoIterator<Item=(usize, usize, u8)> {
        // Find out which values have to be different for each square.
        let mut friends = Vec::with_capacity(81);
        for i in 0 .. 9 {
            for j in 0 .. 9 {
                let row = (0 .. 9).map(|x| (x, i));
                let column = (0 .. 9).map(|y| (j, y));

                let (y, x) = ((i / 3 * 3), (j / 3 * 3));
                let square = [
                    (x, y),   (x+1, y),   (x+2, y),
                    (x, y+1), (x+1, y+1), (x+2, y+1),
                    (x, y+2), (x+1, y+2), (x+2, y+2),
                ];
                let square = square.iter().map(|p| *p);

                let fries = column.chain(row).chain(square)
                    .filter(|&(x, y)| !(x == j && y == i))
                    .map(|(x, y)| 9 * y + x)
                    .collect();

                friends.push(fries);
            }
        }

        let given = given.into_iter().map(|(x, y, n)| {
            if x < 10 && y < 10 && n >= 1 && n <= 9 {
                Ok((x as u8, y as u8, n))
            } else if n >= 1 && n <= 9 {
                Err(CreationError::InvalidPosition(x, y))
            } else {
                Err(CreationError::InvalidNumber(n))
            }
        }).collect::<Result<Vec<_>, _>>()?;

        Ok(Sudoku {
            given,
            possible: [FieldSet::all(); 81],
            board: [0; 81],
            friends,
        })
    }

    /// Solve the sudoku if it has a solution.
    pub fn solve(&mut self) -> Option<Solution> {
        // Set and forward check the given fields.
        for i in 0 .. self.given.len() {
            let (x, y, n) = self.given[i];
            self.possible[(9 * y + x) as usize] = FieldSet::exactly(n);
            self.check_forward(9 * y + x, n);
        }

        // Do a depth-first search.
        let mut stack = Vec::new();
        let mut k: usize = 0;
        while k < 81 {
            if let Some(value) = self.possible[k].take() {
                stack.push((self.possible.clone(), self.board.clone()));

                // Do forward checking with this value.
                if self.check_forward(k as u8, value) {
                    self.board[k] = value;
                    k += 1;
                    continue;
                }
            } else {
                // Go back one level and if this is not possible,
                // the sudoku has no solution.
                if k == 0 {
                    return None;
                }
                k -= 1;
            }

            // Restore the state before the forward checking.
            if let Some((possible, board)) = stack.pop() {
                self.possible = possible;
                self.board = board;
            } else {
                return None;
            }
        }

        Some(Solution {
            board: self.board
        })
    }

    /// Remove the values that got impossible and return
    /// whether there are any left.
    fn check_forward(&mut self, index: u8, value: u8) -> bool {
        for &friend in &self.friends[index as usize] {
            if friend > index {
                let target = &mut self.possible[friend as usize];
                target.remove(value);
                if target.is_empty() {
                    return false;
                }
            }
        }
        true
    }
}

impl Display for Sudoku {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write_board_with(f, &self.board, |f, &field| {
            if field > 0 && field <= 9  {
                write!(f, "{}", field)
            } else {
                write!(f, "_")
            }
        })
    }
}

impl Debug for Sudoku {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl Index<(u8, u8)> for Sudoku {
    type Output = u8;

    /// Get the value at the column `x` and row `y` starting at zero.
    /// If the value is zero this field has no value yet.
    #[inline]
    fn index(&self, (x, y): (u8, u8)) -> &u8 {
        &self.board[(9 * y + x) as usize]
    }
}

/// The solution of a sudoku.
#[derive(Clone)]
pub struct Solution {
    board: [u8; 81],
}

impl Index<(u8, u8)> for Solution {
    type Output = u8;

    /// Get the value at the column `x` and row `y` starting at zero.
    #[inline]
    fn index(&self, (x, y): (u8, u8)) -> &u8 {
        &self.board[(9 * y + x) as usize]
    }
}

impl Display for Solution {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write_board_with(f, &self.board, |f, num| write!(f, "{}", num))
    }
}

impl Debug for Solution {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Copy, Clone)]
struct FieldSet(u16);

impl FieldSet {
    /// A set containing all possibilities from 1 to 9.
    fn all() -> FieldSet {
        FieldSet(0b0000_0011_1111_1110)
    }

    /// Exactly a number.
    fn exactly(num: u8) -> FieldSet {
        FieldSet(1 << num)
    }

    /// Whether there are any possibilities left.
    fn is_empty(&self) -> bool {
        self.0 == 0
    }

    /// Whether this set contains `num`.
    fn contains(&self, num: u8) -> bool {
        self.0 & (1 << num) != 0
    }

    /// Remove the possibilty `num` from the set.
    fn remove(&mut self, num: u8) {
        self.0 &= !(1 << num);
    }

    /// Take any of the possibilities out of the set.
    fn take(&mut self) -> Option<u8> {
        for num in 1 ..= 9 {
            if self.contains(num) {
                self.remove(num);
                return Some(num);
            }
        }
        None
    }
}

impl Debug for FieldSet {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for num in 1 ..= 9 {
            if self.contains(num) {
                if !first { write!(f, "|")?; }
                first = false;
                write!(f, "{}", num)?;
            }
        }
        write!(f, "}}")
    }
}

/// Write out a board writing each field with `writer`.
fn write_board_with<F, T>(f: &mut Formatter, board: &[T], writer: F) -> fmt::Result
    where F: Fn(&mut Formatter, &T) -> fmt::Result {
    for i in 0 .. 9 {
        for j in 0 .. 9 {
            writer(f, &board[(9 * i + j) as usize])?;
            if j < 9 { write!(f, " ")?; }
        }
        if i < 9 { write!(f, "\n")?; }
    }
    Ok(())
}

/// Errors happening at creation of sudokus.
pub enum CreationError {
    /// The position of a given field is not a valid sudoku field.
    InvalidPosition(usize, usize),
    /// A number was not in range `1 ..= 9`.
    InvalidNumber(u8),
}

impl Display for CreationError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CreationError::InvalidPosition(x, y) => write!(f, "invalid position: ({}, {})", x, y),
            CreationError::InvalidNumber(n) => write!(f, "invalid number: {}", n),
        }
    }
}

impl Debug for CreationError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl std::error::Error for CreationError {}

/// Simplifies creation of a sudoku board as shown in the example.
///
/// # Panics
/// If one of the number is out of range `1 ..= 9`.
#[macro_export]
macro_rules! sudoku {
    ($a1:tt $b1:tt $c1:tt $d1:tt $e1:tt $f1:tt $g1:tt $h1:tt $i1:tt
     $a2:tt $b2:tt $c2:tt $d2:tt $e2:tt $f2:tt $g2:tt $h2:tt $i2:tt
     $a3:tt $b3:tt $c3:tt $d3:tt $e3:tt $f3:tt $g3:tt $h3:tt $i3:tt
     $a4:tt $b4:tt $c4:tt $d4:tt $e4:tt $f4:tt $g4:tt $h4:tt $i4:tt
     $a5:tt $b5:tt $c5:tt $d5:tt $e5:tt $f5:tt $g5:tt $h5:tt $i5:tt
     $a6:tt $b6:tt $c6:tt $d6:tt $e6:tt $f6:tt $g6:tt $h6:tt $i6:tt
     $a7:tt $b7:tt $c7:tt $d7:tt $e7:tt $f7:tt $g7:tt $h7:tt $i7:tt
     $a8:tt $b8:tt $c8:tt $d8:tt $e8:tt $f8:tt $g8:tt $h8:tt $i8:tt
     $a9:tt $b9:tt $c9:tt $d9:tt $e9:tt $f9:tt $g9:tt $h9:tt $i9:tt) => {{
        macro_rules! s { ($num:expr) => { $num }; (_) => { 0 }; }
        $crate::Sudoku::from_board(&[
            s!($a1), s!($b1), s!($c1), s!($d1), s!($e1), s!($f1), s!($g1), s!($h1), s!($i1),
            s!($a2), s!($b2), s!($c2), s!($d2), s!($e2), s!($f2), s!($g2), s!($h2), s!($i2),
            s!($a3), s!($b3), s!($c3), s!($d3), s!($e3), s!($f3), s!($g3), s!($h3), s!($i3),
            s!($a4), s!($b4), s!($c4), s!($d4), s!($e4), s!($f4), s!($g4), s!($h4), s!($i4),
            s!($a5), s!($b5), s!($c5), s!($d5), s!($e5), s!($f5), s!($g5), s!($h5), s!($i5),
            s!($a6), s!($b6), s!($c6), s!($d6), s!($e6), s!($f6), s!($g6), s!($h6), s!($i6),
            s!($a7), s!($b7), s!($c7), s!($d7), s!($e7), s!($f7), s!($g7), s!($h7), s!($i7),
            s!($a8), s!($b8), s!($c8), s!($d8), s!($e8), s!($f8), s!($g8), s!($h8), s!($i8),
            s!($a9), s!($b9), s!($c9), s!($d9), s!($e9), s!($f9), s!($g9), s!($h9), s!($i9),
        ]).expect("invalid input for sudoku!")
    }};
}


#[cfg(test)]
mod tests {
    use super::*;

    /// Test whether the solver finds the given solution.
    fn check(sudoku: &mut Sudoku, solution: &[u8; 81]) {
        let solved = sudoku.solve().unwrap();
        assert_eq!(&solved.board[..], &solution[..]);
    }

    #[test]
    fn test_5() {
        let mut sudoku = sudoku! [
            _ _ 5 _ _ 3 _ _ 2
            _ 7 _ _ 6 _ _ 3 _
            1 _ _ 8 _ _ 6 _ _
            _ _ 1 _ _ 6 _ _ 7
            _ 2 _ _ 4 _ _ 6 _
            9 _ _ 2 _ _ 5 _ _
            _ _ 2 _ _ 7 _ _ 4
            _ 1 _ _ 5 _ _ 9 _
            6 _ _ 3 _ _ 2 _ _
        ];

        check(&mut sudoku, &[
            8, 6, 5, 7, 9, 3, 4, 1, 2,
            2, 7, 4, 1, 6, 5, 9, 3, 8,
            1, 3, 9, 8, 2, 4, 6, 7, 5,
            4, 5, 1, 9, 3, 6, 8, 2, 7,
            7, 2, 3, 5, 4, 8, 1, 6, 9,
            9, 8, 6, 2, 7, 1, 5, 4, 3,
            5, 9, 2, 6, 1, 7, 3, 8, 4,
            3, 1, 8, 4, 5, 2, 7, 9, 6,
            6, 4, 7, 3, 8, 9, 2, 5, 1,
        ]);
    }

    #[test]
    fn test_6() {
        let mut sudoku = sudoku! [
            _ 6 4 2 _ _ 9 3 _
            _ _ _ 6 _ _ _ _ _
            _ 3 _ 7 _ _ _ 1 _
            _ _ _ _ _ _ 6 7 2
            _ _ _ _ 1 _ _ _ _
            8 9 2 _ _ _ _ _ _
            _ 5 _ _ _ 4 _ 9 _
            _ _ _ _ _ 8 _ _ _
            _ 1 9 _ _ 7 3 4 _
        ];

        check(&mut sudoku, &[
            7, 6, 4, 2, 8, 1, 9, 3, 5,
            9, 8, 1, 6, 5, 3, 7, 2, 4,
            2, 3, 5, 7, 4, 9, 8, 1, 6,
            1, 4, 3, 8, 9, 5, 6, 7, 2,
            5, 7, 6, 3, 1, 2, 4, 8, 9,
            8, 9, 2, 4, 7, 6, 1, 5, 3,
            3, 5, 8, 1, 6, 4, 2, 9, 7,
            4, 2, 7, 9, 3, 8, 5, 6, 1,
            6, 1, 9, 5, 2, 7, 3, 4, 8,
        ]);
    }

    #[test]
    fn test_7() {
        let mut sudoku = sudoku! [
            _ _ 5 2 _ _ 3 _ _
            _ _ 1 _ _ _ _ _ _
            9 _ _ _ 3 7 _ 6 2
            _ _ 2 _ _ _ _ _ 1
            _ _ 8 _ 4 _ 9 _ _
            3 _ _ _ _ _ 4 _ _
            4 1 _ 3 6 _ _ _ 9
            _ _ _ _ _ _ 7 _ _
            _ _ 9 _ _ 8 5 _ _
        ];

        check(&mut sudoku, &[
            7, 6, 5, 2, 8, 1, 3, 9, 4,
            2, 3, 1, 4, 9, 6, 8, 5, 7,
            9, 8, 4, 5, 3, 7, 1, 6, 2,
            5, 4, 2, 8, 7, 9, 6, 3, 1,
            1, 7, 8, 6, 4, 3, 9, 2, 5,
            3, 9, 6, 1, 5, 2, 4, 7, 8,
            4, 1, 7, 3, 6, 5, 2, 8, 9,
            8, 5, 3, 9, 2, 4, 7, 1, 6,
            6, 2, 9, 7, 1, 8, 5, 4, 3,
        ]);
    }
}
