# Sudoku

Tree-searching _Sudoku_ solver using forward checking. 🎲

### Example
```rust
use sudoku::sudoku;

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

let solution = sudoku.solve().unwrap();
println!("{}", solution);
```

### License
This project is MIT-licensed.
