// SPDX-FileCopyrightText: 2023 SAP SE or an SAP affiliate company and Spheric contributors
// SPDX-License-Identifier: Apache-2.0

package xiter

import (
	"cmp"
	"container/list"
	"context"
	"fmt"
	"iter"
	"slices"
	"strings"
)

// Concat concatenates multiple Seq into a single Seq.
func Concat[V any](seqs ...iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		for _, seq := range seqs {
			for v := range seq {
				if !yield(v) {
					return
				}
			}
		}
	}
}

// Concat2 concatenates multiple Seq2 into a single Seq2.
func Concat2[K, V any](seqs ...iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for _, seq := range seqs {
			for k, v := range seq {
				if !yield(k, v) {
					return
				}
			}
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
func Zip[V1, V2 any](seq1 iter.Seq[V1], seq2 iter.Seq[V2]) iter.Seq[Zipped[V1, V2]] {
	return func(yield func(Zipped[V1, V2]) bool) {
		next, stop := iter.Pull(seq2)
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

func Unzip[V1, V2 any](seq iter.Seq[Zipped[V1, V2]]) (iter.Seq[V1], iter.Seq[V2], func()) {
	var (
		next, stop = iter.Pull(seq)
		v1s, v2s   = list.New(), list.New()
	)
	it1 := func(yield func(V1) bool) {
		for v1s.Len() > 0 {
			head := v1s.Remove(v1s.Front()).(V1)
			if !yield(head) {
				return
			}
		}
		z, ok := next()
		if !ok {
			return
		}
		if z.Ok2 {
			v2s.PushBack(z.V2)
		}
		if z.Ok1 {
			if !yield(z.V1) {
				return
			}
		}
	}
	it2 := func(yield func(V2) bool) {
		for v2s.Len() > 0 {
			head := v2s.Remove(v2s.Front()).(V2)
			if !yield(head) {
				return
			}
		}
		z, ok := next()
		if !ok {
			return
		}
		if z.Ok1 {
			v1s.PushBack(z.V1)
		}
		if z.Ok2 {
			if !yield(z.V2) {
				return
			}
		}
	}
	return it1, it2, stop
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
func Zip2[K1, V1, K2, V2 any](seq1 iter.Seq2[K1, V1], seq2 iter.Seq2[K2, V2]) iter.Seq[Zipped2[K1, V1, K2, V2]] {
	return func(yield func(Zipped2[K1, V1, K2, V2]) bool) {
		next, stop := iter.Pull2(seq2)
		defer stop()

		k2, v2, ok2 := next()
		for k1, v1 := range seq1 {
			if !yield(Zipped2[K1, V1, K2, V2]{k1, v1, true, k2, v2, ok2}) {
				return
			}

			k2, v2, ok2 = next()
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

func Unzip2[K1, V1, K2, V2 any](seq iter.Seq[Zipped2[K1, V1, K2, V2]]) (iter.Seq2[K1, V1], iter.Seq2[K2, V2], func()) {
	var (
		next, stop = iter.Pull(seq)
		kv1s, kv2s = list.New(), list.New()
	)
	it1 := func(yield func(K1, V1) bool) {
		for kv1s.Len() > 0 {
			head := kv1s.Remove(kv1s.Front()).(kv[K1, V1])
			if !yield(head.k, head.v) {
				return
			}
		}
		z, ok := next()
		if !ok {
			return
		}
		if z.Ok2 {
			kv2s.PushBack(kv[K2, V2]{z.K2, z.V2})
		}
		if z.Ok1 {
			if !yield(z.K1, z.V1) {
				return
			}
		}
	}
	it2 := func(yield func(K2, V2) bool) {
		for kv2s.Len() > 0 {
			head := kv2s.Remove(kv2s.Front()).(kv[K2, V2])
			if !yield(head.k, head.v) {
				return
			}
		}
		z, ok := next()
		if !ok {
			return
		}
		if z.Ok1 {
			kv1s.PushBack(kv[K1, V1]{z.K1, z.V1})
		}
		if z.Ok2 {
			if !yield(z.K2, z.V2) {
				return
			}
		}
	}
	return it1, it2, stop
}

// Merge returns a sequence that is the result of merging both sequence values. If one of both sequences
// do not yield a value anymore, the sequence returns.
func Merge[K, V any](seq1 iter.Seq[K], seq2 iter.Seq[V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		next, stop := iter.Pull(seq2)
		defer stop()

		for k := range seq1 {
			v, ok := next()
			if !ok {
				return
			}

			if !yield(k, v) {
				return
			}
		}
	}
}

func MergeAllFunc[K, V any](seq1 iter.Seq[K], seq2 iter.Seq[V], defV1Func func() K, defV2Func func() V) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		next, stop := iter.Pull(seq2)
		defer stop()

		for k := range seq1 {
			v, ok := next()
			if !ok {
				v = defV2Func()
			}

			if !yield(k, v) {
				return
			}
		}
		for {
			v, ok := next()
			if !ok {
				return
			}

			k := defV1Func()
			if !yield(k, v) {
				return
			}
		}
	}
}

func MergeAll[K, V any](seq1 iter.Seq[K], seq2 iter.Seq[V], defV1 K, defV2 V) iter.Seq2[K, V] {
	return MergeAllFunc(seq1, seq2, func() K { return defV1 }, func() V { return defV2 })
}

func Separate[K, V any](seq iter.Seq2[K, V]) (iter.Seq[K], iter.Seq[V], func()) {
	var (
		c1         = list.New()
		c2         = list.New()
		next, stop = iter.Pull2(seq)
	)

	it1 := func(yield func(K) bool) {
		for c1.Len() > 0 {
			k := c1.Remove(c1.Front()).(K)
			if !yield(k) {
				return
			}
		}
		for {
			k, v, ok := next()
			if !ok {
				return
			}

			c2.PushBack(v)
			if !yield(k) {
				return
			}
		}
	}
	it2 := func(yield func(V) bool) {
		for c2.Len() > 0 {
			v := c2.Remove(c2.Front()).(V)
			if !yield(v) {
				return
			}
		}
		for {
			k, v, ok := next()
			if !ok {
				return
			}

			c1.PushBack(k)
			if !yield(v) {
				return
			}
		}
	}

	return it1, it2, stop
}

// Equal checks if two Seq sequences are equal by iterating and checking if both have the same length and values.
func Equal[V comparable](seq1, seq2 iter.Seq[V]) bool {
	for z := range Zip(seq1, seq2) {
		if z.Ok1 != z.Ok2 || z.V1 != z.V2 {
			return false
		}
	}
	return true
}

// Equal2 checks if two Seq2 sequences are equal by iterating and checking if both have the same length and values.
func Equal2[K, V comparable](seq1, seq2 iter.Seq2[K, V]) bool {
	for z := range Zip2(seq1, seq2) {
		if z.Ok1 != z.Ok2 || z.K1 != z.K2 || z.V1 != z.V2 {
			return false
		}
	}
	return true
}

func EqualFunc[V1, V2 any](seq1 iter.Seq[V1], seq2 iter.Seq[V2], f func(V1, V2) bool) bool {
	for z := range Zip(seq1, seq2) {
		if z.Ok1 != z.Ok2 || !f(z.V1, z.V2) {
			return false
		}
	}
	return true
}

func EqualFunc2[K1, V1, K2, V2 any](seq1 iter.Seq2[K1, V1], seq2 iter.Seq2[K2, V2], f func(K1, V1, K2, V2) bool) bool {
	for z := range Zip2(seq1, seq2) {
		if z.Ok1 != z.Ok2 || !f(z.K1, z.V1, z.K2, z.V2) {
			return false
		}
	}
	return true
}

func Foreach[V any](f func(V), seq iter.Seq[V]) {
	for v := range seq {
		f(v)
	}
}

func Foreach2[K, V any](f func(K, V), seq iter.Seq2[K, V]) {
	for k, v := range seq {
		f(k, v)
	}
}

func Tap[V any](f func(V), seq iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		for v := range seq {
			f(v)
			if !yield(v) {
				return
			}
		}
	}
}

func Tap2[K, V any](f func(K, V), seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range seq {
			f(k, v)
			if !yield(k, v) {
				return
			}
		}
	}
}

func TapKey[K, V any](f func(K), seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Tap2(func(k K, v V) { f(k) }, seq)
}

func TapValue[K, V any](f func(V), seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Tap2(func(k K, v V) { f(v) }, seq)
}

func Filter[V any](f func(V) bool, seq iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		for v := range seq {
			if f(v) {
				if !yield(v) {
					return
				}
			}
		}
	}
}

func Filter2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range seq {
			if f(k, v) {
				if !yield(k, v) {
					return
				}
			}
		}
	}
}

func FilterKey[K, V any](f func(K) bool, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Filter2(func(k K, _ V) bool { return f(k) }, seq)
}

func FilterValue[K, V any](f func(V) bool, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Filter2(func(_ K, v V) bool { return f(v) }, seq)
}

func FilterNotEqual[V comparable](notEq V, seq iter.Seq[V]) iter.Seq[V] {
	return Filter(func(v V) bool {
		return v != notEq
	}, seq)
}

func FilterNotEqual2[K, V comparable](kNotEq K, vNotEq V, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Filter2(func(k K, v V) bool {
		return kNotEq != k && vNotEq != v
	}, seq)
}

func FilterKeyNotEqual[K comparable, V any](kNotEq K, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Filter2(func(k K, v V) bool {
		return kNotEq != k
	}, seq)
}

func FilterValueNotEqual[K any, V comparable](vNotEq V, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return Filter2(func(k K, v V) bool {
		return vNotEq != v
	}, seq)
}

func Find[V any](f func(V) bool, seq iter.Seq[V]) (V, bool) {
	for v := range seq {
		if f(v) {
			return v, true
		}
	}
	var zero V
	return zero, false
}

func Find2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) (K, V, bool) {
	for k, v := range seq {
		if f(k, v) {
			return k, v, true
		}
	}
	var (
		zeroK K
		zeroV V
	)
	return zeroK, zeroV, false
}

func FindByKey[K, V any](f func(K) bool, seq iter.Seq2[K, V]) (K, V, bool) {
	return Find2(func(k K, v V) bool { return f(k) }, seq)
}

func FindByValue[K, V any](f func(V) bool, seq iter.Seq2[K, V]) (K, V, bool) {
	return Find2(func(k K, v V) bool { return f(v) }, seq)
}

func Contains[V comparable](seq iter.Seq[V], needle V) bool {
	for v := range seq {
		if v == needle {
			return true
		}
	}
	return false
}

func Contains2[K, V comparable](seq iter.Seq2[K, V], needleK K, needleV V) bool {
	for k, v := range seq {
		if needleK == k && needleV == v {
			return true
		}
	}
	return false
}

func ContainsFunc[V any](f func(V) bool, seq iter.Seq[V]) bool {
	for v := range seq {
		if f(v) {
			return true
		}
	}
	return false
}

func ContainsFunc2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) bool {
	for k, v := range seq {
		if f(k, v) {
			return true
		}
	}
	return false
}

func Take[V any](n int, seq iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		var i int
		for v := range seq {
			if i >= n {
				return
			}

			i++
			if !yield(v) {
				return
			}
		}
	}
}

func Take2[K, V any](n int, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		var i int
		for k, v := range seq {
			if i >= n {
				return
			}

			i++
			if !yield(k, v) {
				return
			}
		}
	}
}

func TakeWhile[V any](f func(V) bool, seq iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		for v := range seq {
			if !f(v) {
				return
			}

			if !yield(v) {
				return
			}
		}
	}
}

func TakeWhile2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range seq {
			if !f(k, v) {
				return
			}

			if !yield(k, v) {
				return
			}
		}
	}
}

func Drop[V any](n int, seq iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		var i int
		for v := range seq {
			if i < n {
				i++
				continue
			}

			if !yield(v) {
				return
			}
		}
	}
}

func Drop2[K, V any](n int, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		var i int
		for k, v := range seq {
			if i < n {
				i++
				continue
			}

			if !yield(k, v) {
				return
			}
		}
	}
}

func DropWhile[V any](f func(V) bool, seq iter.Seq[V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		drop := true
		for v := range seq {
			if drop {
				if f(v) {
					continue
				}
				drop = false
			}

			if !yield(v) {
				return
			}
		}
	}
}

func DropWhile2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		drop := true
		for k, v := range seq {
			if drop {
				if f(k, v) {
					continue
				}
				drop = false
			}

			if !yield(k, v) {
				return
			}
		}
	}
}

func GroupedNoCopy[V any](n int, seq iter.Seq[V]) iter.Seq[[]V] {
	if n <= 0 {
		panic("GroupedNoCopy: n must be greater than 0")
	}

	return func(yield func([]V) bool) {
		vs := make([]V, 0, n)
		for v := range seq {
			vs = append(vs, v)
			if len(vs) == n {
				if !yield(vs) {
					return
				}

				vs = vs[:0]
			}
		}
		if len(vs) > 0 {
			yield(vs)
		}
	}
}

func Grouped[V any](n int, seq iter.Seq[V]) iter.Seq[[]V] {
	if n <= 0 {
		panic("Grouped: n must be greater than 0")
	}

	return func(yield func([]V) bool) {
		vs := make([]V, 0, n)
		for v := range seq {
			vs = append(vs, v)
			if len(vs) == n {
				if !yield(vs) {
					return
				}

				vs = make([]V, 0, n)
			}
		}
		if len(vs) > 0 {
			yield(vs)
		}
	}
}

func Map[In, Out any](f func(In) Out, seq iter.Seq[In]) iter.Seq[Out] {
	return func(yield func(Out) bool) {
		for v := range seq {
			if !yield(f(v)) {
				return
			}
		}
	}
}

func Map2[KIn, VIn, KOut, VOut any](f func(KIn, VIn) (KOut, VOut), seq iter.Seq2[KIn, VIn]) iter.Seq2[KOut, VOut] {
	return func(yield func(KOut, VOut) bool) {
		for k, v := range seq {
			if !yield(f(k, v)) {
				return
			}
		}
	}
}

func Flatmap[In, Out any](f func(In) iter.Seq[Out], seq iter.Seq[In]) iter.Seq[Out] {
	return func(yield func(Out) bool) {
		for v := range seq {
			for vi := range f(v) {
				if !yield(vi) {
					return
				}
			}
		}
	}
}

func Flatmap2[KIn, VIn, KOut, VOut any](f func(KIn, VIn) iter.Seq2[KOut, VOut], seq iter.Seq2[KIn, VIn]) iter.Seq2[KOut, VOut] {
	return func(yield func(KOut, VOut) bool) {
		for k, v := range seq {
			for ki, vi := range f(k, v) {
				if !yield(ki, vi) {
					return
				}
			}
		}
	}
}

func Flatten[V any](seq iter.Seq[iter.Seq[V]]) iter.Seq[V] {
	return func(yield func(V) bool) {
		for s := range seq {
			for v := range s {
				if !yield(v) {
					return
				}
			}
		}
	}
}

func Flatten2[K, V any](seq iter.Seq[iter.Seq2[K, V]]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for s := range seq {
			for k, v := range s {
				if !yield(k, v) {
					return
				}
			}
		}
	}
}

func Reduce[Sum, V any](sum Sum, f func(Sum, V) Sum, seq iter.Seq[V]) Sum {
	for v := range seq {
		sum = f(sum, v)
	}
	return sum
}

func Reduce2[Sum, K, V any](sum Sum, f func(Sum, K, V) Sum, seq iter.Seq2[K, V]) Sum {
	for k, v := range seq {
		sum = f(sum, k, v)
	}
	return sum
}

func Keys[K, V any](seq iter.Seq2[K, V]) iter.Seq[K] {
	return func(yield func(K) bool) {
		for k, _ := range seq {
			if !yield(k) {
				return
			}
		}
	}
}

func Values[K, V any](seq iter.Seq2[K, V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		for _, v := range seq {
			if !yield(v) {
				return
			}
		}
	}
}

func MapLift[In, KOut, VOut any](f func(In) (KOut, VOut), seq iter.Seq[In]) iter.Seq2[KOut, VOut] {
	return func(yield func(KOut, VOut) bool) {
		for v := range seq {
			if !yield(f(v)) {
				return
			}
		}
	}
}

func MapLower[KIn, VIn, VOut any](f func(KIn, VIn) VOut, seq iter.Seq2[KIn, VIn]) iter.Seq[VOut] {
	return func(yield func(VOut) bool) {
		for k, v := range seq {
			if !yield(f(k, v)) {
				return
			}
		}
	}
}

func MapErr[In, Out any](f func(In) (Out, error), seq iter.Seq[In]) iter.Seq2[Out, error] {
	return MapLift[In, Out, error](f, seq)
}

func TryCollect[K any](it iter.Seq2[K, error]) ([]K, error) {
	var res []K
	for k, err := range it {
		if err != nil {
			return res, err
		}

		res = append(res, k)
	}
	return res, nil
}

func Swap[K, V any](seq iter.Seq2[K, V]) iter.Seq2[V, K] {
	return func(yield func(V, K) bool) {
		for k, v := range seq {
			if !yield(v, k) {
				return
			}
		}
	}
}

func MapKeys[KIn, V, KOut any](f func(KIn) KOut, seq iter.Seq2[KIn, V]) iter.Seq2[KOut, V] {
	return Map2(func(k KIn, v V) (KOut, V) {
		return f(k), v
	}, seq)
}

func MapValues[K, VIn, VOut any](f func(VIn) VOut, seq iter.Seq2[K, VIn]) iter.Seq2[K, VOut] {
	return Map2(func(k K, v VIn) (K, VOut) {
		return k, f(v)
	}, seq)
}

func Repeat[V any](v V, n int) iter.Seq[V] {
	return func(yield func(V) bool) {
		for i := 0; i < n; i++ {
			if !yield(v) {
				return
			}
		}
	}
}

func Repeat2[K, V any](k K, v V, n int) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for i := 0; i < n; i++ {
			if !yield(k, v) {
				return
			}
		}
	}
}

func Cache[V any](seq iter.Seq[V]) (res iter.Seq[V], stop func()) {
	var (
		vs      []V
		cached  bool
		next    func() (V, bool)
		stopSeq func()
	)
	return func(yield func(V) bool) {
			for _, v := range vs {
				if !yield(v) {
					return
				}
			}
			if cached {
				return
			}

			if next == nil {
				next, stopSeq = iter.Pull(seq)
			}

			for {
				v, ok := next()
				if !ok {
					break
				}

				vs = append(vs, v)
				if !yield(v) {
					break
				}
			}
			cached = true
			stopSeq()
			stopSeq = nil
		}, func() {
			if stopSeq != nil {
				stopSeq()
				stopSeq = nil
			}
		}
}

func Cycle[V any](seq iter.Seq[V]) (iter.Seq[V], func()) {
	cachedSeq, stop := Cache(seq)

	return func(yield func(V) bool) {
		for {
			for v := range cachedSeq {
				if !yield(v) {
					return
				}
			}
		}
	}, stop
}

type kv[K, V any] struct {
	k K
	v V
}

func Cache2[K, V any](seq iter.Seq2[K, V]) (res iter.Seq2[K, V], stop func()) {
	var (
		kvs     []kv[K, V]
		cached  bool
		next    func() (K, V, bool)
		stopSeq func()
	)
	return func(yield func(K, V) bool) {
			for _, v := range kvs {
				if !yield(v.k, v.v) {
					return
				}
			}
			if cached {
				return
			}

			if next == nil {
				next, stopSeq = iter.Pull2(seq)
			}

			for {
				k, v, ok := next()
				if !ok {
					break
				}

				kvs = append(kvs, kv[K, V]{k, v})
				if !yield(k, v) {
					break
				}
			}
			cached = true
			stop()
			stop = nil
		}, func() {
			if stopSeq != nil {
				stopSeq()
				stopSeq = nil
			}
		}
}

func Cycle2[K, V any](seq iter.Seq2[K, V]) (res iter.Seq2[K, V], stop func()) {
	cachedSeq, stop := Cache2(seq)

	return func(yield func(K, V) bool) {
		for {
			for k, v := range cachedSeq {
				if !yield(k, v) {
					return
				}
			}
		}
	}, stop
}

func Enumerate[V any](seq iter.Seq[V]) iter.Seq2[int, V] {
	return func(yield func(int, V) bool) {
		i := 0
		for v := range seq {
			if !yield(i, v) {
				return
			}
			i++
		}
	}
}

func All[V any](f func(V) bool, seq iter.Seq[V]) bool {
	for v := range seq {
		if !f(v) {
			return false
		}
	}
	return true
}

func All2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) bool {
	for k, v := range seq {
		if !f(k, v) {
			return false
		}
	}
	return true
}

func Any[V any](f func(V) bool, seq iter.Seq[V]) bool {
	for v := range seq {
		if f(v) {
			return true
		}
	}
	return false
}

func Any2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) bool {
	for k, v := range seq {
		if f(k, v) {
			return true
		}
	}
	return false
}

func Count[V any](f func(V) bool, seq iter.Seq[V]) int {
	var n int
	for v := range seq {
		if f(v) {
			n++
		}
	}
	return n
}

func Count2[K, V any](f func(K, V) bool, seq iter.Seq2[K, V]) int {
	var n int
	for k, v := range seq {
		if f(k, v) {
			n++
		}
	}
	return n
}

func Len[V any](s iter.Seq[V]) int {
	var n int
	for v := range s {
		_ = v
		n++
	}
	return n
}

func Len2[K, V any](s iter.Seq2[K, V]) int {
	var n int
	for k, v := range s {
		_, _ = k, v
		n++
	}
	return n
}

func Index[V any](idx int, seq iter.Seq[V]) V {
	if idx < 0 {
		panic("Index: negative index")
	}

	var i int
	for v := range seq {
		if i == idx {
			return v
		}
		i++
	}
	panic(fmt.Sprintf("Index: index %d out of bounds", idx))
}

func Index2[K, V any](idx int, seq iter.Seq2[K, V]) (K, V) {
	if idx < 0 {
		panic("Index2: negative index")
	}

	var i int
	for k, v := range seq {
		if i == idx {
			return k, v
		}
		i++
	}
	panic(fmt.Sprintf("Index2: index %d out of bounds", idx))
}

func Of[V any](vs ...V) iter.Seq[V] {
	return OfSlice(vs)
}

func OfKVs[K, V any](kvs ...any) iter.Seq2[K, V] {
	return OfKVSlice[K, V](kvs)
}

func OfMap[M ~map[K]V, K comparable, V any](m M) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		for k, v := range m {
			if !yield(k, v) {
				return
			}
		}
	}
}

func OfMapKeys[M ~map[K]V, K comparable, V any](m M) iter.Seq[K] {
	return func(yield func(K) bool) {
		for k := range m {
			if !yield(k) {
				return
			}
		}
	}
}

func OfMapValues[M ~map[K]V, K comparable, V any](m M) iter.Seq[V] {
	return func(yield func(V) bool) {
		for _, v := range m {
			if !yield(v) {
				return
			}
		}
	}
}

func OfSlice[S ~[]V, V any](s S) iter.Seq[V] {
	return slices.Values(s)
}

func OfKVSlice[K, V any, S ~[]any](s S) iter.Seq2[K, V] {
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

func OfSliceIndex[S ~[]V, V any](s S) iter.Seq2[int, V] {
	return func(yield func(int, V) bool) {
		for i, v := range s {
			if !yield(i, v) {
				return
			}
		}
	}
}

func OfChan[C interface{ ~<-chan V | ~chan V }, V any](c C) iter.Seq[V] {
	return func(yield func(V) bool) {
		for v := range c {
			if !yield(v) {
				return
			}
		}
	}
}

func OfNext[V any](f func() (V, bool)) iter.Seq[V] {
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

func OfNext2[K, V any](f func() (K, V, bool)) iter.Seq2[K, V] {
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

func Empty[V any]() iter.Seq[V] {
	return func(_ func(V) bool) {}
}

func Empty2[K, V any]() iter.Seq2[K, V] {
	return func(_ func(K, V) bool) {}
}

func Receive[C interface{ ~<-chan V | chan V }, V any](ctx context.Context, c C) iter.Seq[V] {
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

func AppendSlice[S ~[]V, V any](s S, seq iter.Seq[V]) S {
	for v := range seq {
		s = append(s, v)
	}
	return s
}

func AppendSlice2[S ~[]V, V any](s S, seq iter.Seq2[V, V]) S {
	for v1, v2 := range seq {
		s = append(s, v1, v2)
	}
	return s
}

func AppendKVSlice2[S ~[]any, K, V any](s S, seq iter.Seq2[K, V]) S {
	for k, v := range seq {
		s = append(s, k, v)
	}
	return s
}

func ToSlice[V any](seq iter.Seq[V]) []V {
	var res []V
	return AppendSlice(res, seq)
}

func ToSlice2[V any](seq iter.Seq2[V, V]) []V {
	var res []V
	return AppendSlice2(res, seq)
}

func ToSliceWithCap[V any](seq iter.Seq[V], cap int) []V {
	res := make([]V, 0, cap)
	return AppendSlice(res, seq)
}

func ToSliceWithCap2[V any](seq iter.Seq2[V, V], cap int) []V {
	res := make([]V, 0, cap)
	return AppendSlice2(res, seq)
}

func ToKVSlice[K, V any](seq iter.Seq2[K, V]) []any {
	var res []any
	return AppendKVSlice2[[]any, K, V](res, seq)
}

func CopyToSlice[S ~[]V, V any](dst S, seq iter.Seq[V]) int {
	n := len(dst)
	if n == 0 {
		return 0
	}

	var i int
	for v := range seq {
		dst[i] = v
		if (i + 1) >= n {
			break
		}
		i++
	}
	return i
}

func SetMap[M ~map[K]V, K comparable, V any](m M, seq iter.Seq2[K, V]) {
	for k, v := range seq {
		m[k] = v
	}
}

func ToMap[K comparable, V any](seq iter.Seq2[K, V]) map[K]V {
	res := make(map[K]V)
	SetMap(res, seq)
	return res
}

func AppendSliceMap[M ~map[K][]V, K comparable, V any](m M, seq iter.Seq2[K, V]) {
	for k, v := range seq {
		m[k] = append(m[k], v)
	}
}

func ToSliceMap[K comparable, V any](seq iter.Seq2[K, V]) map[K][]V {
	res := make(map[K][]V)
	AppendSliceMap(res, seq)
	return res
}

func IntoChan[C ~chan<- V, V any](c C, seq iter.Seq[V]) {
	for v := range seq {
		c <- v
	}
}

func Send[C interface{ ~chan<- V | chan V }, V any](ctx context.Context, c C, seq iter.Seq[V]) {
	for v := range seq {
		select {
		case <-ctx.Done():
			return
		case c <- v:
		}
	}
}

func ToChan[V any](seq iter.Seq[V]) <-chan V {
	c := make(chan V)
	go func() {
		for v := range seq {
			c <- v
		}
	}()
	return c
}

func SendChan[V any](ctx context.Context, seq iter.Seq[V]) <-chan V {
	c := make(chan V)
	go func() {
		for v := range seq {
			select {
			case <-ctx.Done():
				return
			case c <- v:
			}
		}
	}()
	return c
}

func ToList[V any](seq iter.Seq[V]) *list.List {
	l := list.New()
	for v := range seq {
		l.PushBack(v)
	}
	return l
}

func Sum[V cmp.Ordered](seq iter.Seq[V]) V {
	var zero V
	return Reduce(zero, func(sum V, v V) V {
		return sum + v
	}, seq)
}

func Max[V cmp.Ordered](seq iter.Seq[V]) V {
	var res *V
	for v := range seq {
		if res == nil || v > *res {
			res = &v
		}
	}
	if res == nil {
		panic("Max: empty Seq")
	}
	return *res
}

func MaxFunc[V cmp.Ordered](seq iter.Seq[V], compare func(a, b V) int) V {
	var res *V
	for v := range seq {
		if res == nil || compare(v, *res) > 0 {
			res = &v
		}
	}
	if res == nil {
		panic("MaxFunc: empty Seq")
	}
	return *res
}

func MaxOk[V cmp.Ordered](seq iter.Seq[V]) (V, bool) {
	var res *V
	for v := range seq {
		if res == nil || v > *res {
			res = &v
		}
	}
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func MaxOkFunc[V cmp.Ordered](seq iter.Seq[V], compare func(a, b V) int) (V, bool) {
	var res *V
	for v := range seq {
		if res == nil || compare(v, *res) > 0 {
			res = &v
		}
	}
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func Min[V cmp.Ordered](seq iter.Seq[V]) V {
	var res *V
	for v := range seq {
		if res == nil || v < *res {
			res = &v
		}
	}
	if res == nil {
		panic("Min: empty Seq")
	}
	return *res
}

func MinFunc[V cmp.Ordered](seq iter.Seq[V], compare func(a, b V) int) V {
	var res *V
	for v := range seq {
		if res == nil || compare(v, *res) < 0 {
			res = &v
		}
	}
	if res == nil {
		panic("MinFunc: empty Seq")
	}
	return *res
}

func MinOk[V cmp.Ordered](seq iter.Seq[V]) (V, bool) {
	var res *V
	for v := range seq {
		if res == nil || v < *res {
			res = &v
		}
	}
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func MinOkFunc[V cmp.Ordered](seq iter.Seq[V], compare func(a, b V) int) (V, bool) {
	var res *V
	for v := range seq {
		if res == nil || compare(v, *res) < 0 {
			res = &v
		}
	}
	if res == nil {
		var zero V
		return zero, false
	}
	return *res, true
}

func rangeInternal(name string, start, end, step int) iter.Seq[int] {
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

func Range(start, end int) iter.Seq[int] {
	return rangeInternal("Range", start, end, 1)
}

func RangeStep(start, end, step int) iter.Seq[int] {
	return rangeInternal("RangeStep", start, end, 1)
}

func Join[V ~string](seq iter.Seq[V], sep string) string {
	var (
		sb   strings.Builder
		tail bool
	)
	for v := range seq {
		if tail {
			sb.WriteString(sep)
		}
		tail = true
		sb.WriteString(string(v))
	}
	return sb.String()
}

func Drain[V any](seq iter.Seq[V]) {
	seq(func(V) bool { return true })
}

func Drain2[K, V any](seq iter.Seq2[K, V]) {
	seq(func(K, V) bool { return true })
}
