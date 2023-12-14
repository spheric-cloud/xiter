package xiter

import (
	"cmp"
	"container/list"
	"context"
	"fmt"
	"strings"
	"sync"
)

type (
	// Seq0 is a function representing a sequence over empty computations.
	// Returning false from a yield function indicates the sequence that the iteration should be terminated.
	Seq0 = func(yield func() bool)
	// Seq is a function representing a sequence of values of type V.
	// Returning false from a yield function indicates the sequence that the iteration should be terminated.
	Seq[V any] func(yield func(V) bool)
	// Seq2 is a function representing a sequence of values of type K and V.
	// Returning false from a yield function indicates the sequence that the iteration should be terminated.
	Seq2[K, V any] func(yield func(K, V) bool)
)

// Concat0 concatenates multiple Seq0 into a single Seq0.
func Concat0(seqs ...Seq0) Seq0 {
	return func(yield func() bool) {
		ok := true
		for _, seq := range seqs {
			seq(func() bool {
				ok = yield()
				return ok
			})
			if !ok {
				return
			}
		}
	}
}

// Concat concatenates multiple Seq into a single Seq.
func Concat[V any](seqs ...Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		ok := true
		for _, seq := range seqs {
			seq(func(v V) bool {
				ok = yield(v)
				return ok
			})
			if !ok {
				return
			}
		}
	}
}

// Concat2 concatenates multiple Seq2 into a single Seq2.
func Concat2[K, V any](seqs ...Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		ok := true
		for _, seq := range seqs {
			seq(func(k K, v V) bool {
				ok = yield(k, v)
				return ok
			})
			if !ok {
				return
			}
		}
	}
}

// Pull0 transforms a Seq0 into a next function and a stop function.
// Pull0 consumes the sequence.
// Calling stop stops the iteration, making the next call to next return false for ok.
func Pull0(seq Seq0) (next func() bool, stop func()) {
	var (
		done   = make(chan struct{})
		prompt = make(chan struct{})
		yield  = make(chan struct{})
		once   sync.Once
	)
	stop = func() {
		once.Do(func() {
			close(done)
		})
	}

	go func() {
		defer close(yield)
		defer stop()

		select {
		case <-done:
			return
		case _, ok := <-prompt:
			if !ok {
				return
			}
		}

		seq(func() bool {
			select {
			case <-done:
				return false
			case yield <- struct{}{}:
				select {
				case <-done:
					return false
				case _, ok := <-prompt:
					return ok
				}
			}
		})
	}()

	next = func() bool {
		select {
		case <-done:
			return false
		case prompt <- struct{}{}:
			select {
			case <-done:
				return false
			case _, ok := <-yield:
				return ok
			}
		}
	}
	return next, stop
}

// Pull transforms a Seq into a next function and a stop function.
// Pull consumes the sequence.
// Calling stop stops the iteration, making the next call to next return false for ok.
func Pull[V any](seq Seq[V]) (next func() (V, bool), stop func()) {
	var (
		done   = make(chan struct{})
		prompt = make(chan struct{})
		yield  = make(chan V)
		once   sync.Once
	)

	stop = func() {
		once.Do(func() {
			close(done)
		})
	}

	go func() {
		defer close(yield)
		defer stop()

		select {
		case <-done:
			return
		case _, ok := <-prompt:
			if !ok {
				return
			}
		}

		seq(func(v V) bool {
			select {
			case <-done:
				return false
			case yield <- v:
				select {
				case <-done:
					return false
				case _, ok := <-prompt:
					return ok
				}
			}
		})
	}()

	next = func() (V, bool) {
		select {
		case <-done:
			var zero V
			return zero, false
		case prompt <- struct{}{}:
			select {
			case <-done:
				var zero V
				return zero, false
			case v, ok := <-yield:
				return v, ok
			}
		}
	}
	return next, stop
}

type kv[K any, V any] struct {
	K K
	V V
}

// Pull2 transforms a Seq2 into a next function and a stop function.
// Pull2 consumes the sequence.
// Calling stop stops the iteration, making the next call to next return false for ok.
func Pull2[K, V any](seq Seq2[K, V]) (next func() (K, V, bool), stop func()) {
	var (
		done   = make(chan struct{})
		prompt = make(chan struct{})
		yield  = make(chan kv[K, V])
		once   sync.Once
	)

	stop = func() {
		once.Do(func() {
			close(done)
		})
	}

	go func() {
		defer close(yield)
		defer stop()

		select {
		case <-done:
			return
		case _, ok := <-prompt:
			if !ok {
				return
			}
		}

		seq(func(k K, v V) bool {
			select {
			case <-done:
				return false
			case yield <- kv[K, V]{k, v}:
				select {
				case <-done:
					return false
				case _, ok := <-prompt:
					return ok
				}
			}
		})
	}()

	next = func() (K, V, bool) {
		select {
		case <-done:
			var (
				zeroK K
				zeroV V
			)
			return zeroK, zeroV, false
		case prompt <- struct{}{}:
			select {
			case <-done:
				var (
					zeroK K
					zeroV V
				)
				return zeroK, zeroV, false
			case kv, ok := <-yield:
				return kv.K, kv.V, ok
			}
		}
	}
	return next, stop
}

// Zipped0 is the resulting sequence type of Zip0.
type Zipped0 struct {
	// Ok1 indicates whether the first sequence had a value at the position.
	Ok1 bool
	// Ok2 indicates whether the second sequence had a value at the position.
	Ok2 bool
}

// Zip0 zips the given sequences together.
// The resulting sequence has the length of the longest length of both sequences.
// The Zipped0 at each position contain indicators whether any sequence had a value or not.
func Zip0(seq1, seq2 Seq0) Seq[Zipped0] {
	return func(yield func(Zipped0) bool) {
		next, stop := Pull0(seq2)
		defer stop()

		ok := true
		ok2 := next()
		seq1(func() bool {
			if !yield(Zipped0{true, ok2}) {
				ok = false
				return false
			}
			ok2 = next()
			return true
		})
		if !ok {
			return
		}

		for ok2 {
			if !yield(Zipped0{false, ok2}) {
				return
			}
			ok2 = next()
		}
	}
}

// Zipped represents a type that holds two values of types V1 and V2 respectively,
// along with boolean flags indicating whether the values are present (Ok1 and Ok2).
type Zipped[V1, V2 any] struct {
	V1  V1
	Ok1 bool

	V2  V2
	Ok2 bool
}

// Zip combines two sequences into a single sequence by yielding zipped pairs of elements from each sequence.
// The returned sequence will produce a Zipped struct for each pair of elements, containing the value and presence flag for each sequence.
// The sequences will be zipped until both sequences are exhausted or the yield function returns false.
// If the yield function returns false, the zipping will stop and the function will return.
// After the first sequence is exhausted, the remaining elements of the second sequence will be paired with default values and presence flags.
func Zip[V1, V2 any](seq1 Seq[V1], seq2 Seq[V2]) Seq[Zipped[V1, V2]] {
	return func(yield func(Zipped[V1, V2]) bool) {
		next, stop := Pull(seq2)
		defer stop()

		ok := true
		v2, ok2 := next()
		seq1(func(v1 V1) bool {
			if !yield(Zipped[V1, V2]{v1, true, v2, ok2}) {
				ok = false
				return false
			}
			v2, ok2 = next()
			return true
		})
		if !ok {
			return
		}

		var v1 V1
		for ok2 {
			if !yield(Zipped[V1, V2]{v1, false, v2, ok2}) {
				return
			}
			v2, ok2 = next()
		}
	}
}

// Zipped2 represents a type that holds two values of types K1, V1 and K2, V2 respectively,
// along with boolean flags indicating whether the values are present (Ok1 and Ok2).
type Zipped2[K1, V1, K2, V2 any] struct {
	K1  K1
	V1  V1
	Ok1 bool

	K2  K2
	V2  V2
	Ok2 bool
}

// Zip2 combines two sequences into a single sequence by yielding zipped pairs of elements from each sequence.
// The returned sequence will produce a Zipped2 struct for each pair of elements, containing the value and presence flag for each sequence.
// The sequences will be zipped until both sequences are exhausted or the yield function returns false.
// If the yield function returns false, the zipping will stop and the function will return.
// After the first sequence is exhausted, the remaining elements of the second sequence will be paired with default values and presence flags.
func Zip2[K1, V1, K2, V2 any](seq1 Seq2[K1, V1], seq2 Seq2[K2, V2]) Seq[Zipped2[K1, V1, K2, V2]] {
	return func(yield func(Zipped2[K1, V1, K2, V2]) bool) {
		next, stop := Pull2(seq2)
		defer stop()

		ok := true
		k2, v2, ok2 := next()
		seq1(func(k1 K1, v1 V1) bool {
			if !yield(Zipped2[K1, V1, K2, V2]{k1, v1, true, k2, v2, ok2}) {
				ok = false
				return false
			}
			k2, v2, ok2 = next()
			return true
		})
		if !ok {
			return
		}

		var (
			k1 K1
			v1 V1
		)
		for ok2 {
			if !yield(Zipped2[K1, V1, K2, V2]{k1, v1, false, k2, v2, ok2}) {
				return
			}
			k2, v2, ok2 = next()
		}
	}
}

// Equal0 checks if two Seq0 sequences are equal by iterating and checking if both have the same length.
func Equal0(seq1, seq2 Seq0) bool {
	ok := true
	Zip0(seq1, seq2)(func(z Zipped0) bool {
		if z.Ok1 != z.Ok2 {
			ok = false
			return false
		}
		return true
	})
	return ok
}

// Equal checks if two Seq sequences are equal by iterating and checking if both have the same length and values.
func Equal[V comparable](seq1, seq2 Seq[V]) bool {
	ok := true
	Zip(seq1, seq2)(func(z Zipped[V, V]) bool {
		if z.Ok1 != z.Ok2 || z.V1 != z.V2 {
			ok = false
			return false
		}
		return true
	})
	return ok
}

// Equal2 checks if two Seq2 sequences are equal by iterating and checking if both have the same length and values.
func Equal2[K, V comparable](seq1, seq2 Seq2[K, V]) bool {
	ok := true
	Zip2(seq1, seq2)(func(z Zipped2[K, V, K, V]) bool {
		if z.Ok1 != z.Ok2 || z.K1 != z.K2 || z.V1 != z.V2 {
			ok = false
			return false
		}
		return true
	})
	return ok
}

func EqualFunc[V1, V2 any](seq1 Seq[V1], seq2 Seq[V2], f func(V1, V2) bool) bool {
	ok := true
	Zip(seq1, seq2)(func(z Zipped[V1, V2]) bool {
		if z.Ok1 != z.Ok2 || !f(z.V1, z.V2) {
			ok = false
			return false
		}
		return true
	})
	return ok
}

func EqualFunc2[K1, V1, K2, V2 any](seq1 Seq2[K1, V1], seq2 Seq2[K2, V2], f func(K1, V1, K2, V2) bool) bool {
	ok := true
	Zip2(seq1, seq2)(func(z Zipped2[K1, V1, K2, V2]) bool {
		if z.Ok1 != z.Ok2 || !f(z.K1, z.V1, z.K2, z.V2) {
			ok = false
			return false
		}
		return true
	})
	return ok
}

func Foreach[V any](f func(V), seq Seq[V]) {
	seq(func(v V) bool {
		f(v)
		return true
	})
}

func Foreach2[K, V any](f func(K, V), seq Seq2[K, V]) {
	seq(func(k K, v V) bool {
		f(k, v)
		return true
	})
}

func Tap[V any](f func(V), seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		seq(func(v V) bool {
			f(v)
			return yield(v)
		})
	}
}

func Tap2[K, V any](f func(K, V), seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(k K, v V) bool {
			f(k, v)
			return yield(k, v)
		})
	}
}

func TapKey[K, V any](f func(K), seq Seq2[K, V]) Seq2[K, V] {
	return Tap2(func(k K, v V) { f(k) }, seq)
}

func TapValue[K, V any](f func(V), seq Seq2[K, V]) Seq2[K, V] {
	return Tap2(func(k K, v V) { f(v) }, seq)
}

func Filter[V any](f func(V) bool, seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		seq(func(v V) bool {
			if f(v) {
				return yield(v)
			}
			return true
		})
	}
}

func Filter2[K, V any](f func(K, V) bool, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(k K, v V) bool {
			if f(k, v) {
				return yield(k, v)
			}
			return true
		})
	}
}

func FilterKey[K, V any](f func(K) bool, seq Seq2[K, V]) Seq2[K, V] {
	return Filter2(func(k K, _ V) bool { return f(k) }, seq)
}

func FilterValue[K, V any](f func(V) bool, seq Seq2[K, V]) Seq2[K, V] {
	return Filter2(func(_ K, v V) bool { return f(v) }, seq)
}

func FilterNotEqual[V comparable](notEq V, seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		seq(func(v V) bool {
			if notEq != v {
				return yield(v)
			}
			return true
		})
	}
}

func FilterNotEqual2[K, V comparable](kNotEq K, vNotEq V, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(k K, v V) bool {
			if kNotEq != k && vNotEq != v {
				return yield(k, v)
			}
			return true
		})
	}
}

func FilterKeyNotEqual[K comparable, V any](kNotEq K, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(k K, v V) bool {
			if kNotEq != k {
				return yield(k, v)
			}
			return true
		})
	}
}

func FilterValueNotEqual[K any, V comparable](vNotEq V, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(k K, v V) bool {
			if vNotEq != v {
				return yield(k, v)
			}
			return true
		})
	}
}

func Find[V any](f func(V) bool, seq Seq[V]) (V, bool) {
	var (
		res V
		ok  bool
	)
	seq(func(v V) bool {
		if f(v) {
			res = v
			ok = true
			return false
		}
		return true
	})
	return res, ok
}

func Find2[K, V any](f func(K, V) bool, seq Seq2[K, V]) (K, V, bool) {
	var (
		resK K
		resV V
		ok   bool
	)
	seq(func(k K, v V) bool {
		if f(k, v) {
			resK = k
			resV = v
			ok = true
			return false
		}
		return true
	})
	return resK, resV, ok
}

func FindByKey[K, V any](f func(K) bool, seq Seq2[K, V]) (K, V, bool) {
	return Find2(func(k K, v V) bool { return f(k) }, seq)
}

func FindByValue[K, V any](f func(V) bool, seq Seq2[K, V]) (K, V, bool) {
	return Find2(func(k K, v V) bool { return f(v) }, seq)
}

func Contains[V comparable](seq Seq[V], v V) bool {
	var ok bool
	seq(func(other V) bool {
		if v == other {
			ok = true
			return false
		}
		return true
	})
	return ok
}

func Contains2[K, V comparable](seq Seq2[K, V], k K, v V) bool {
	var ok bool
	seq(func(otherK K, otherV V) bool {
		if k == otherK && v == otherV {
			ok = true
			return false
		}
		return true
	})
	return ok
}

func ContainsFunc[V any](f func(V) bool, seq Seq[V]) bool {
	var ok bool
	seq(func(v V) bool {
		if f(v) {
			ok = true
			return false
		}
		return true
	})
	return ok
}

func ContainsFunc2[K, V any](f func(K, V) bool, seq Seq2[K, V]) bool {
	var ok bool
	seq(func(k K, v V) bool {
		if f(k, v) {
			ok = true
			return false
		}
		return true
	})
	return ok
}

func Take0(n int, seq Seq0) Seq0 {
	return func(yield func() bool) {
		i := 0
		seq(func() bool {
			if i < n {
				i++
				return yield()
			}
			return false
		})
	}
}

func Take[V any](n int, seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		i := 0
		seq(func(v V) bool {
			if i < n {
				i++
				return yield(v)
			}
			return false
		})
	}
}

func Take2[K, V any](n int, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		i := 0
		seq(func(k K, v V) bool {
			if i < n {
				i++
				return yield(k, v)
			}
			return false
		})
	}
}

func TakeWhile[V any](f func(V) bool, seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		seq(func(v V) bool {
			if !f(v) {
				return false
			}

			return yield(v)
		})
	}
}

func TakeWhile2[K, V any](f func(K, V) bool, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(k K, v V) bool {
			if !f(k, v) {
				return false
			}

			return yield(k, v)
		})
	}
}

func Drop[V any](n int, seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		i := 0
		seq(func(v V) bool {
			if i < n {
				i++
				return true
			}

			return yield(v)
		})
	}
}

func Drop2[K, V any](n int, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		i := 0
		seq(func(k K, v V) bool {
			if i < n {
				i++
				return true
			}

			return yield(k, v)
		})
	}
}

func DropWhile[V any](f func(V) bool, seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		drop := true

		seq(func(v V) bool {
			if drop {
				if f(v) {
					return true
				}
				drop = false
			}
			return yield(v)
		})
	}
}

func DropWhile2[K, V any](f func(K, V) bool, seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		drop := true

		seq(func(k K, v V) bool {
			if drop {
				if f(k, v) {
					return true
				}
				drop = false
			}
			return yield(k, v)
		})
	}
}

func Grouped[V any](n int, seq Seq[V]) Seq[[]V] {
	if n <= 0 {
		panic("Grouped: n must be greater than 0")
	}

	return func(yield func([]V) bool) {
		var (
			vs = make([]V, 0, n)
			ok = true
		)
		seq(func(v V) bool {
			vs = append(vs, v)
			if len(vs) == n {
				ok = yield(vs)
				vs = nil
				return ok
			}
			return true
		})
		if !ok {
			return
		}

		// Check if there is a remainder group and if so yield it..
		if len(vs) > 0 {
			// we don't need to check yield here as we're returning anyways.
			yield(vs)
		}
	}
}

func Map[In, Out any](f func(In) Out, seq Seq[In]) Seq[Out] {
	return func(yield func(Out) bool) {
		seq(func(in In) bool {
			return yield(f(in))
		})
	}
}

func Map2[KIn, VIn, KOut, VOut any](f func(KIn, VIn) (KOut, VOut), seq Seq2[KIn, VIn]) Seq2[KOut, VOut] {
	return func(yield func(KOut, VOut) bool) {
		seq(func(kIn KIn, vIn VIn) bool {
			return yield(f(kIn, vIn))
		})
	}
}

func Flatmap[In, Out any](f func(In) Seq[Out], seq Seq[In]) Seq[Out] {
	return func(yield func(Out) bool) {
		seq(func(in In) bool {
			ok := true
			f(in)(func(out Out) bool {
				ok = yield(out)
				return ok
			})
			return ok
		})
	}
}

func Flatmap2[KIn, VIn, KOut, VOut any](f func(KIn, VIn) Seq2[KOut, VOut], seq Seq2[KIn, VIn]) Seq2[KOut, VOut] {
	return func(yield func(KOut, VOut) bool) {
		seq(func(kIn KIn, vIn VIn) bool {
			ok := true
			f(kIn, vIn)(func(kOut KOut, vOut VOut) bool {
				ok = yield(kOut, vOut)
				return ok
			})
			return ok
		})
	}
}

func Flatten[V any](seq Seq[Seq[V]]) Seq[V] {
	return func(yield func(V) bool) {
		seq(func(s Seq[V]) bool {
			ok := true
			s(func(v V) bool {
				ok = yield(v)
				return ok
			})
			return ok
		})
	}
}

func Flatten2[K, V any](seq Seq[Seq2[K, V]]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		seq(func(s Seq2[K, V]) bool {
			ok := true
			s(func(k K, v V) bool {
				ok = yield(k, v)
				return ok
			})
			return ok
		})
	}
}

func Reduce[Sum, V any](sum Sum, f func(Sum, V) Sum, seq Seq[V]) Sum {
	seq(func(v V) bool {
		sum = f(sum, v)
		return true
	})
	return sum
}

func Reduce2[Sum, K, V any](sum Sum, f func(Sum, K, V) Sum, seq Seq2[K, V]) Sum {
	seq(func(k K, v V) bool {
		sum = f(sum, k, v)
		return true
	})
	return sum
}

func Keys[K, V any](seq Seq2[K, V]) Seq[K] {
	return func(yield func(K) bool) {
		seq(func(k K, _ V) bool {
			return yield(k)
		})
	}
}

func Values[K, V any](seq Seq2[K, V]) Seq[V] {
	return func(yield func(V) bool) {
		seq(func(_ K, v V) bool {
			return yield(v)
		})
	}
}

func MapLift[In, KOut, VOut any](f func(In) (KOut, VOut), seq Seq[In]) Seq2[KOut, VOut] {
	return func(yield func(KOut, VOut) bool) {
		seq(func(in In) bool {
			return yield(f(in))
		})
	}
}

func MapLower[KIn, VIn, VOut any](f func(KIn, VIn) VOut, seq Seq2[KIn, VIn]) Seq[VOut] {
	return func(yield func(VOut) bool) {
		seq(func(k KIn, v VIn) bool {
			return yield(f(k, v))
		})
	}
}

func MapErr[In, Out any](f func(In) (Out, error), seq Seq[In]) Seq2[Out, error] {
	return MapLift[In, Out, error](f, seq)
}

func Swap[K, V any](seq Seq2[K, V]) Seq2[V, K] {
	return func(yield func(V, K) bool) {
		seq(func(k K, v V) bool {
			return yield(v, k)
		})
	}
}

func MapKeys[KIn, V, KOut any](f func(KIn) KOut, seq Seq2[KIn, V]) Seq2[KOut, V] {
	return Map2(func(k KIn, v V) (KOut, V) {
		return f(k), v
	}, seq)
}

func MapValues[K, VIn, VOut any](f func(VIn) VOut, seq Seq2[K, VIn]) Seq2[K, VOut] {
	return Map2(func(k K, v VIn) (K, VOut) {
		return k, f(v)
	}, seq)
}

func Repeat[V any](v V, n int) Seq[V] {
	return func(yield func(V) bool) {
		for i := 0; i < n; i++ {
			if !yield(v) {
				return
			}
		}
	}
}

func Repeat2[K, V any](k K, v V, n int) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for i := 0; i < n; i++ {
			if !yield(k, v) {
				return
			}
		}
	}
}

func Cache[V any](seq Seq[V]) Seq[V] {
	var vs []V
	return func(yield func(V) bool) {
		if vs != nil {
			OfSlice(vs)(yield)
			return
		}

		vs = []V{}
		seq(func(v V) bool {
			vs = append(vs, v)
			return yield(v)
		})
	}
}

func Cycle[V any](seq Seq[V]) Seq[V] {
	return func(yield func(V) bool) {
		var vs []V

		ok := true
		seq(func(v V) bool {
			ok = yield(v)
			if ok {
				vs = append(vs, v)
			}
			return ok
		})
		if !ok {
			return
		}
		if len(vs) == 0 {
			return
		}

		for i := 0; true; i = (i + 1) % len(vs) {
			if !yield(vs[i]) {
				return
			}
		}
	}
}

func Cycle2[K, V any](seq Seq2[K, V]) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		var kvs []kv[K, V]

		ok := true
		seq(func(k K, v V) bool {
			ok = yield(k, v)
			if ok {
				kvs = append(kvs, kv[K, V]{k, v})
			}
			return ok
		})
		if !ok {
			return
		}
		if len(kvs) == 0 {
			return
		}

		for i := 0; true; i = (i + 1) % len(kvs) {
			kv := &kvs[i]
			if !yield(kv.K, kv.V) {
				return
			}
		}
	}
}

func Enumerate[V any](seq Seq[V]) Seq2[int, V] {
	return func(yield func(int, V) bool) {
		i := 0
		seq(func(v V) bool {
			if !yield(i, v) {
				return false
			}
			i++
			return true
		})
	}
}

func All[V any](f func(V) bool, seq Seq[V]) bool {
	ok := true
	seq(func(v V) bool {
		if !f(v) {
			ok = false
			return false
		}
		return true
	})
	return ok
}

func All2[K, V any](f func(K, V) bool, seq Seq2[K, V]) bool {
	ok := true
	seq(func(k K, v V) bool {
		if !f(k, v) {
			ok = false
			return false
		}
		return true
	})
	return ok
}

func Any[V any](f func(V) bool, seq Seq[V]) bool {
	ok := false
	seq(func(v V) bool {
		if f(v) {
			ok = true
			return false
		}
		return true
	})
	return ok
}

func Any2[K, V any](f func(K, V) bool, seq Seq2[K, V]) bool {
	ok := false
	seq(func(k K, v V) bool {
		if f(k, v) {
			ok = true
			return false
		}
		return true
	})
	return ok
}

func Count[V any](f func(V) bool, seq Seq[V]) int {
	n := 0
	seq(func(v V) bool {
		if f(v) {
			n++
		}
		return true
	})
	return n
}

func Count2[K, V any](f func(K, V) bool, seq Seq2[K, V]) int {
	n := 0
	seq(func(k K, v V) bool {
		if f(k, v) {
			n++
		}
		return true
	})
	return n
}

func Len0(s Seq0) int {
	var l int
	s(func() bool {
		l++
		return true
	})
	return l
}

func Len[V any](s Seq[V]) int {
	var l int
	s(func(V) bool {
		l++
		return true
	})
	return l
}

func Len2[K, V any](s Seq2[K, V]) int {
	var l int
	s(func(K, V) bool {
		l++
		return true
	})
	return l
}

func Index[V any](idx int, seq Seq[V]) V {
	if idx < 0 {
		panic("Index: negative index")
	}

	var (
		res V
		i   int
		ok  bool
	)
	seq(func(v V) bool {
		if i == idx {
			res = v
			ok = true
			return false
		}
		i++
		return true
	})
	if !ok {
		panic(fmt.Sprintf("Index %d out of bounds", idx))
	}
	return res
}

func Index2[K, V any](idx int, seq Seq2[K, V]) (K, V) {
	if idx < 0 {
		panic("Index2: negative index")
	}

	var (
		resK K
		resV V
		ok   bool
		i    int
	)
	seq(func(k K, v V) bool {
		if i == idx {
			resK = k
			resV = v
			ok = true
			return false
		}
		i++
		return true
	})
	if !ok {
		panic(fmt.Sprintf("Index %d out of bounds", idx))
	}
	return resK, resV
}

func Of[V any](vs ...V) Seq[V] {
	return OfSlice(vs)
}

func OfKVs[K, V any](kvs ...any) Seq2[K, V] {
	return OfKVSlice[K, V](kvs)
}

func OfMap[M ~map[K]V, K comparable, V any](m M) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range m {
			if !yield(k, v) {
				return
			}
		}
	}
}

func OfMapKeys[M ~map[K]V, K comparable, V any](m M) Seq[K] {
	return func(yield func(K) bool) {
		for k := range m {
			if !yield(k) {
				return
			}
		}
	}
}

func OfMapValues[M ~map[K]V, K comparable, V any](m M) Seq[V] {
	return func(yield func(V) bool) {
		for _, v := range m {
			if !yield(v) {
				return
			}
		}
	}
}

func OfSlice[S ~[]V, V any](s S) Seq[V] {
	return func(yield func(V) bool) {
		for _, v := range s {
			if !yield(v) {
				return
			}
		}
	}
}

func OfKVSlice[K, V any, S ~[]any](s S) Seq2[K, V] {
	if len(s)%2 != 0 {
		panic(fmt.Sprintf("OfSlice: unmatched number of elements (%d)", len(s)))
	}
	return func(yield func(K, V) bool) {
		for i := 0; i < len(s); i += 2 {
			if !yield(s[i].(K), s[i+1].(V)) {
				return
			}
		}
	}
}

func OfSliceIndex[S ~[]V, V any](s S) Seq2[int, V] {
	return func(yield func(int, V) bool) {
		for i, v := range s {
			if !yield(i, v) {
				return
			}
		}
	}
}

func OfChan[C interface{ ~<-chan V | ~chan V }, V any](c C) Seq[V] {
	return func(yield func(V) bool) {
		for v := range c {
			if !yield(v) {
				return
			}
		}
	}
}

func OfNext[V any](f func() (V, bool)) Seq[V] {
	return func(yield func(V) bool) {
		for {
			v, ok := f()
			if !ok {
				return
			}
			if !yield(v) {
				return
			}
		}
	}
}

func OfNext2[K, V any](f func() (K, V, bool)) Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for {
			k, v, ok := f()
			if !ok {
				return
			}
			if !yield(k, v) {
				return
			}
		}
	}
}

func Empty0() Seq0 {
	return func(_ func() bool) {}
}

func Empty[V any]() Seq[V] {
	return func(_ func(V) bool) {}
}

func Empty2[K, V any]() Seq2[K, V] {
	return func(_ func(K, V) bool) {}
}

func Receive[C interface{ ~<-chan V | chan V }, V any](ctx context.Context, c C) Seq[V] {
	return func(yield func(V) bool) {
		for {
			select {
			case <-ctx.Done():
				return
			case v, ok := <-c:
				if !ok {
					return
				}
				if !yield(v) {
					return
				}
			}
		}
	}
}

func AppendSlice[S ~[]V, V any](s S, seq Seq[V]) S {
	seq(func(v V) bool {
		s = append(s, v)
		return true
	})
	return s
}

func AppendSlice2[S ~[]any, K, V any](s S, seq Seq2[K, V]) S {
	seq(func(k K, v V) bool {
		s = append(s, k, v)
		return true
	})
	return s
}

func ToSlice[V any](seq Seq[V]) []V {
	var res []V
	return AppendSlice(res, seq)
}

func ToKVSlice[K, V any](seq Seq2[K, V]) []any {
	var res []any
	return AppendSlice2[[]any, K, V](res, seq)
}

func CopyToSlice[S ~[]V, V any](dst S, seq Seq[V]) int {
	n := len(dst)
	if n == 0 {
		return 0
	}

	i := 0
	seq(func(v V) bool {
		dst[i] = v
		if (i + 1) >= n {
			return false
		}
		i++
		return true
	})
	return i
}

func SetMap[M ~map[K]V, K comparable, V any](m M, seq Seq2[K, V]) {
	seq(func(k K, v V) bool {
		m[k] = v
		return true
	})
}

func ToMap[K comparable, V any](seq Seq2[K, V]) map[K]V {
	res := make(map[K]V)
	seq(func(k K, v V) bool {
		res[k] = v
		return true
	})
	return res
}

func AppendSliceMap[M ~map[K][]V, K comparable, V any](m M, seq Seq2[K, V]) {
	seq(func(k K, v V) bool {
		m[k] = append(m[k], v)
		return true
	})
}

func ToSliceMap[K comparable, V any](seq Seq2[K, V]) map[K][]V {
	res := make(map[K][]V)
	seq(func(k K, v V) bool {
		res[k] = append(res[k], v)
		return true
	})
	return res
}

func IntoChan[C ~chan<- V, V any](c C, seq Seq[V]) {
	seq(func(v V) bool {
		c <- v
		return true
	})
}

func Send[C interface{ ~chan<- V | chan V }, V any](ctx context.Context, c C, seq Seq[V]) {
	seq(func(v V) bool {
		select {
		case <-ctx.Done():
			return false
		case c <- v:
			return true
		}
	})
}

func ToChan[V any](seq Seq[V]) <-chan V {
	c := make(chan V)
	go func() {
		seq(func(v V) bool {
			c <- v
			return true
		})
	}()
	return c
}

func SendChan[V any](ctx context.Context, seq Seq[V]) <-chan V {
	c := make(chan V)
	go func() {
		seq(func(v V) bool {
			select {
			case <-ctx.Done():
				return false
			case c <- v:
				return true
			}
		})
	}()
	return c
}

func ToList[V any](seq Seq[V]) *list.List {
	l := list.New()
	seq(func(v V) bool {
		l.PushBack(v)
		return true
	})
	return l
}

func Sum[V cmp.Ordered](seq Seq[V]) V {
	var sum V
	seq(func(v V) bool {
		sum += v
		return true
	})
	return sum
}

func Max[V cmp.Ordered](seq Seq[V]) V {
	var res *V
	seq(func(v V) bool {
		if res == nil || v > *res {
			res = &v
		}
		return true
	})
	if res == nil {
		panic("xiter.Max on empty Seq")
	}
	return *res
}

func MaxFunc[V cmp.Ordered](seq Seq[V], compare func(a, b V) int) V {
	var res *V
	seq(func(v V) bool {
		if res == nil || compare(v, *res) > 0 {
			res = &v
		}
		return true
	})
	if res == nil {
		panic("xiter.MaxFunc on empty Seq")
	}
	return *res
}

func MaxOk[V cmp.Ordered](seq Seq[V]) (V, bool) {
	var res *V
	seq(func(v V) bool {
		if res == nil || v > *res {
			res = &v
		}
		return true
	})
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func MaxOkFunc[V cmp.Ordered](seq Seq[V], compare func(a, b V) int) (V, bool) {
	var res *V
	seq(func(v V) bool {
		if res == nil || compare(v, *res) > 0 {
			res = &v
		}
		return true
	})
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func Min[V cmp.Ordered](seq Seq[V]) V {
	var res *V
	seq(func(v V) bool {
		if res == nil || v < *res {
			res = &v
		}
		return true
	})
	if res == nil {
		panic("xiter.Min on empty Seq")
	}
	return *res
}

func MinFunc[V cmp.Ordered](seq Seq[V], compare func(a, b V) int) V {
	var res *V
	seq(func(v V) bool {
		if res == nil || compare(v, *res) < 0 {
			res = &v
		}
		return true
	})
	if res == nil {
		panic("xiter.MinFunc on empty Seq")
	}
	return *res
}

func MinOk[V cmp.Ordered](seq Seq[V]) (V, bool) {
	var res *V
	seq(func(v V) bool {
		if res == nil || v < *res {
			res = &v
		}
		return true
	})
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func MinOkFunc[V cmp.Ordered](seq Seq[V], compare func(a, b V) int) (V, bool) {
	var res *V
	seq(func(v V) bool {
		if res == nil || compare(v, *res) < 0 {
			res = &v
		}
		return true
	})
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func rangeInternal(name string, start, end, step int) Seq[int] {
	if step == 0 {
		panic(fmt.Sprintf("xiter.%s step cannot be zero", name))
	}
	if start < end && step < 0 || start > end && step > 0 {
		panic(fmt.Sprintf("xiter.%s %d to %d step %d is not a valid range", name, start, end, step))
	}
	return func(yield func(int) bool) {
		for i := start; i < end; i++ {
			if !yield(i) {
				return
			}
		}
	}
}

func Range(start, end int) Seq[int] {
	return rangeInternal("Range", start, end, 1)
}

func RangeStep(start, end, step int) Seq[int] {
	return rangeInternal("RangeStep", start, end, 1)
}

func Join[V ~string](seq Seq[V], sep string) string {
	var (
		sb   strings.Builder
		tail bool
	)
	seq(func(v V) bool {
		if tail {
			sb.WriteString(sep)
		}
		tail = true
		sb.WriteString(string(v))
		return true
	})
	return sb.String()
}

func Drain0(seq Seq0) {
	seq(func() bool { return true })
}

func Drain[V any](seq Seq[V]) {
	seq(func(V) bool { return true })
}

func Drain2[K, V any](seq Seq2[K, V]) {
	seq(func(K, V) bool { return true })
}
