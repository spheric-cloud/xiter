# xiter
[![Go Reference](https://pkg.go.dev/badge/spheric.cloud/xiter.svg)](https://pkg.go.dev/spheric.cloud/xiter)

`xiter` is a Go package offering a variety of tools for sequence manipulation and functional-style operations on sequences. It provides a range of functions for concatenation, transformation, filtering, searching, and more, for different types of sequences.

## Installation

To install `xiter`, use the following command:

```bash
go get spheric.cloud/xiter
```

## Usage

Here's an example demonstrating some functionalities of `xiter`:

```go
package main

import (
    "fmt"
    "spheric.cloud/xiter"
)

func main() {
    // Example: Concatenating two sequences
    seq1 := xiter.Of(1, 2, 3)
    seq2 := xiter.Of(4, 5, 6)
    concatenated := xiter.Concat(seq1, seq2)
    fmt.Println("Concatenated Sequence:", xiter.ToSlice(concatenated))

    // Example: Filtering a sequence
    filtered := xiter.Filter(func(v int) bool { return v%2 == 0 }, concatenated)
    fmt.Println("Filtered Sequence (Even Numbers):", xiter.ToSlice(filtered))

    // Example: Mapping a sequence
    mapped := xiter.Map(func(v int) int { return v * v }, filtered)
    fmt.Println("Mapped Sequence (Squared Values):", xiter.ToSlice(mapped))
}
```

## API Reference

The `xiter` package includes a variety of types and functions, such as:

- Sequence types: `Seq0`, `Seq[V]`, `Seq2[K, V]`
- Concatenation functions: `Concat0`, `Concat[V]`, `Concat2[K, V]`
- Transformation functions: `Pull0`, `Pull[V]`, `Pull2[K, V]`
- Zipping functions: `Zip0`, `Zip[V1, V2]`, `Zip2[K1, V1, K2, V2]`
- Utility functions: `Equal0`, `Equal[V]`, `Equal2[K, V]`, `Foreach[V]`, `Map[In, Out]`

For full documentation, visit [pkg.go.dev](https://pkg.go.dev/spheric.cloud/xiter).

## Contributing

Contributions to `xiter` are welcome! Please refer to the contributing guidelines for more information.

## License

`xiter` is licensed under the [MIT License](LICENSE).
