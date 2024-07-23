package xiter_test

import (
	"context"
	"maps"
	"math/rand"
	"reflect"
	"slices"
	. "spheric.cloud/xiter"
	"strconv"
	"testing"
)

func AbsMod(n int, cap int) int {
	return Abs(n) % cap
}

func Abs(n int) int {
	if n < 0 {
		return n * -1
	}
	return n
}

func MkYield0(calls *int, n int) func() bool {
	return func() bool {
		*calls++

		if n < 0 {
			return true
		}
		return *calls < n
	}
}

func MkYield[V any](elems *[]V, n int) func(V) bool {
	return func(e V) bool {
		*elems = append(*elems, e)

		if n < 0 {
			return true
		}
		return len(*elems) < n
	}
}

func MkYield2[K, V any](elems *[]any, n int) func(K, V) bool {
	return func(k K, v V) bool {
		*elems = append(*elems, k, v)

		if n < 0 {
			return true
		}
		return len(*elems) < n*2
	}
}

func MkSeq0(calls *int, n int) Seq0 {
	return func(yield func() bool) {
		for *calls = 0; *calls < n; *calls++ {
			if !yield() {
				return
			}
		}
	}
}

func MkRandSlice(n int) []int {
	res := make([]int, n)
	for i := 0; i < n; i++ {
		res[i] = rand.Int()
	}
	return res
}

func MkRandKVSlice(n int) []any {
	res := make([]any, n*2)
	for i := 0; i < n*2; i += 2 {
		res[i] = rand.Int()
		res[i+1] = rand.Int()
	}
	return res
}

func MkRandSeq(n int) Seq[int] {
	return OfSlice(MkRandSlice(n))
}

func MkRandSeq2(n int) Seq2[int, int] {
	return OfKVSlice[int, int](MkRandKVSlice(n))
}

func EqualIgnoreOrder[V any](s1, s2 []V) bool {
	if len(s1) != len(s2) {
		return false
	}

	visited := make([]bool, len(s2))
	for _, v1 := range s1 {
		found := false
		for j, v2 := range s2 {
			if !visited[j] && reflect.DeepEqual(v1, v2) {
				visited[j] = true
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}
func TestConcat0(t *testing.T) {
	testCases := []struct {
		name   string
		ns     []int
		yieldN int
		want   int
	}{
		{"empty seq", []int{}, -1, 0},
		{"single seq", []int{4}, -1, 4},
		{"multiple seqs", []int{4, 3}, -1, 7},
		{"multiple seqs early return", []int{4, 3}, 5, 5},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			seqCalls := make([]int, len(tc.ns))
			seqs := make([]Seq0, len(tc.ns))
			for i := 0; i < len(tc.ns); i++ {
				seqs[i] = MkSeq0(&seqCalls[i], tc.ns[i])
			}
			seq := Concat0(seqs...)

			var ans int
			yield := MkYield0(&ans, tc.yieldN)
			seq(yield)

			if ans != tc.want {
				t.Errorf("got %d calls, expected %d", ans, tc.want)
			}

			for i := 0; ans > 0 && i < len(seqCalls); i++ {
				wantCalls := min(ans, seqCalls[i])
				if seqCalls[i] != wantCalls {
					t.Errorf("seq %d got %d calls, expected %d", i, seqCalls[i], wantCalls)
				}

				ans = ans - wantCalls
			}
		})
	}
}

func TestConcat(t *testing.T) {
	testCases := []struct {
		name   string
		ss     [][]int
		yieldN int
		want   []int
	}{
		{"Empty seq", [][]int{}, -1, []int{}},
		{"Single seq", [][]int{{1}}, 1, []int{1}},
		{"Multiple seqs", [][]int{{1, 2}, {3, 4}}, -1, []int{1, 2, 3, 4}},
		{"Multiple seqs early return", [][]int{{1, 2}, {3, 4}}, 3, []int{1, 2, 3}},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			seqs := make([]Seq[int], len(tc.ss))
			for i := 0; i < len(tc.ss); i++ {
				seqs[i] = OfSlice(tc.ss[i])
			}

			s := Concat(seqs...)
			var ans []int
			yield := MkYield(&ans, tc.yieldN)
			s(yield)

			if !slices.Equal(ans, tc.want) {
				t.Errorf("got %v, expected %v (yield %d)", ans, tc.want, tc.yieldN)
			}
		})
	}
}

func TestConcat2(t *testing.T) {
	testCases := []struct {
		name   string
		ss     [][]any
		yieldN int
		want   []any
	}{
		{"Empty seq", [][]any{}, -1, nil},
		{"Single seq", [][]any{{"foo", 1}}, -1, []any{"foo", 1}},
		{"Multiple seqs", [][]any{{"foo", 1}, {"bar", 2}, {"baz", 3}}, -1, []any{"foo", 1, "bar", 2, "baz", 3}},
		{"Multiple seqs early return", [][]any{{"foo", 1}, {"bar", 2}, {"baz", 3}}, 2, []any{"foo", 1, "bar", 2}},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			seqs := make([]Seq2[string, int], len(tc.ss))

			for i := 0; i < len(tc.ss); i++ {
				seqs[i] = OfKVSlice[string, int](tc.ss[i])
			}

			s := Concat2(seqs...)
			var ans []any
			yield := MkYield2[string, int](&ans, tc.yieldN)
			s(yield)

			if !reflect.DeepEqual(ans, tc.want) {
				t.Errorf("got %v, expected %v (yield %d)", ans, tc.want, tc.yieldN)
			}
		})
	}
}

func FuzzEqual(f *testing.F) {
	testCases := []int{
		0, 1, 4, 10,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}

	f.Fuzz(func(t *testing.T, n int) {
		// cap n at 20
		n %= 20

		s := MkRandSlice(n)

		i1, i2 := OfSlice(s), OfSlice(s)

		if !Equal(i1, i2) {
			t.Errorf("Expected slices of %v to be equal", s)
		}
	})
}

func FuzzOfSlice(f *testing.F) {
	testCases := []int{
		0, 1, 4, 10,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}

	f.Fuzz(func(t *testing.T, n int) {
		// cap n at 20
		n %= 20

		s := make([]int, n)
		for i := 0; i < n; i++ {
			s[i] = rand.Int()
		}

		var res []int
		OfSlice(s)(func(i int) bool {
			res = append(res, i)
			return true
		})

		if !slices.Equal(s, res) {
			t.Errorf("Expected slice %v but got %v", s, res)
		}
	})
}

func TestPull0(t *testing.T) {
	testCases := []struct {
		name  string
		n     int
		stopN int
		want  int
	}{
		{"no elems", 0, -1, 0},
		{"ten elems", 10, -1, 10},
		{"stop early", 10, 5, 5},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			var ans int
			next, stop := Pull0(MkSeq0(&ans, tc.n))
			defer stop()

			for {
				if tc.stopN != -1 && tc.stopN == ans {
					stop()
				}

				if !next() {
					break
				}
			}

			if ans != tc.want {
				t.Errorf("got %d calls, expected %d", ans, tc.want)
			}
		})
	}
}

func TestPull(t *testing.T) {
	testCases := []struct {
		name  string
		s     []int
		stopN int
		want  []int
	}{
		{"no elems", []int{}, -1, []int{}},
		{"some elems", []int{1, 2, 3}, -1, []int{1, 2, 3}},
		{"stop early", []int{1, 2, 3}, 2, []int{1, 2}},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			var ans []int
			next, stop := Pull(OfSlice(tc.s))
			defer stop()

			for {
				if tc.stopN != -1 && tc.stopN == len(ans) {
					stop()
				}

				v, ok := next()
				if !ok {
					break
				}

				ans = append(ans, v)
			}

			if !slices.Equal(ans, tc.want) {
				t.Errorf("got %v, expected %v", ans, tc.want)
			}
		})
	}
}

func TestPull2(t *testing.T) {
	testCases := []struct {
		name  string
		s     []any
		stopN int
		want  []any
	}{
		{"no elems", []any{}, -1, []any{}},
		{"some elems", []any{"foo", 1, "bar", 2, "baz", 3}, -1, []any{"foo", 1, "bar", 2, "baz", 3}},
		{"stop early", []any{"foo", 1, "bar", 2, "baz", 3}, 2, []any{"foo", 1, "bar", 2}},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			var ans []any
			next, stop := Pull2(OfKVSlice[string, int](tc.s))
			defer stop()

			for {
				if tc.stopN != -1 && tc.stopN*2 == len(ans) {
					stop()
				}

				k, v, ok := next()
				if !ok {
					break
				}

				ans = append(ans, k, v)
			}

			if !slices.Equal(ans, tc.want) {
				t.Errorf("got %v, expected %v", ans, tc.want)
			}
		})
	}
}

func FuzzZip0(f *testing.F) {
	testCases := []struct {
		n1, n2 int
	}{
		{3, 3},
		{0, 0},
		{1, 3},
		{3, 1},
	}
	for _, tc := range testCases {
		f.Add(tc.n1, tc.n2)
	}

	f.Fuzz(func(t *testing.T, n1, n2 int) {
		if n1 < 0 || n2 < 0 {
			t.Skip()
		}

		n1 %= 20
		n2 %= 20
		n := max(n1, n2)

		for i := 0; i < n; i++ {
			seq := Zip0(MkSeq0(new(int), n1), MkSeq0(new(int), n2))
			if i != n-1 {
				seq = Take(i, seq)
			}

			ans := ToSlice(seq)
			for i := 0; i < len(ans); i++ {
				wantOk1 := i < n1
				if ans[i].Ok1 != wantOk1 {
					t.Errorf("got %t for ok1 %d but expected %t", ans[i].Ok1, i, wantOk1)
				}

				wantOk2 := i < n2
				if ans[i].Ok2 != wantOk2 {
					t.Errorf("got %t for ok2 %d but expected %t", ans[i].Ok2, i, wantOk2)
				}
			}
		}
	})
}

func FuzzZip(f *testing.F) {
	testCases := []struct {
		n1, n2 int
	}{
		{3, 3},
		{0, 0},
		{1, 3},
		{3, 1},
	}
	for _, tc := range testCases {
		f.Add(tc.n1, tc.n2)
	}

	f.Fuzz(func(t *testing.T, n1, n2 int) {
		if n1 < 0 || n2 < 0 {
			t.Skip()
		}

		n1 %= 20
		n2 %= 20
		n := max(n1, n2)
		v1 := MkRandSlice(n1)
		v2 := MkRandSlice(n2)

		for i := 0; i < n; i++ {
			seq := Zip(OfSlice(v1), OfSlice(v2))
			if i != n-1 {
				seq = Take(i, seq)
			}

			ans := ToSlice(seq)
			for i := 0; i < len(ans); i++ {
				wantOk1 := i < n1
				if ans[i].Ok1 != wantOk1 {
					t.Errorf("got %t for ok1 %d but expected %t", ans[i].Ok1, i, wantOk1)
				} else if wantOk1 {
					if ans[i].V1 != v1[i] {
						t.Errorf("got %v for v1 %d but expected %v", ans[i].V1, i, v1[i])
					}
				}

				wantOk2 := i < n2
				if ans[i].Ok2 != wantOk2 {
					t.Errorf("got %t for ok2 %d but expected %t", ans[i].Ok2, i, wantOk2)
				} else if wantOk2 {
					if ans[i].V2 != v2[i] {
						t.Errorf("got %v for v2 %d but expected %v", ans[i].V2, i, v2[i])
					}
				}
			}
		}
	})
}

func FuzzZip2(f *testing.F) {
	testCases := []struct {
		n1, n2 int
	}{
		{3, 3},
		{0, 0},
		{1, 3},
		{3, 1},
	}
	for _, tc := range testCases {
		f.Add(tc.n1, tc.n2)
	}

	f.Fuzz(func(t *testing.T, n1, n2 int) {
		if n1 < 0 || n2 < 0 {
			t.Skip()
		}

		n1 %= 20
		n2 %= 20
		n := max(n1, n2)
		kvs1 := MkRandKVSlice(n1)
		kvs2 := MkRandKVSlice(n2)

		for i := 0; i < n; i++ {
			seq := Zip2(OfKVSlice[int, int](kvs1), OfKVSlice[int, int](kvs2))
			if i != n-1 {
				seq = Take(i, seq)
			}

			ans := ToSlice(seq)
			for i := 0; i < len(ans); i++ {
				ki := i * 2
				vi := i*2 + 1

				wantOk1 := i < n1
				if ans[i].Ok1 != wantOk1 {
					t.Errorf("got %t for ok1 %d but expected %t", ans[i].Ok1, i, wantOk1)
				} else if wantOk1 {
					if ans[i].K1 != kvs1[ki] {
						t.Errorf("got %v for v1.k1 %d but expected %v", ans[i].V1, i, kvs1[ki])
					}
					if ans[i].V1 != kvs1[vi] {
						t.Errorf("got %v for v1.v1 %d but expected %v", ans[i].V1, i, kvs1[vi])
					}
				}

				wantOk2 := i < n2
				if ans[i].Ok2 != wantOk2 {
					t.Errorf("got %t for ok2 %d but expected %t", ans[i].Ok2, i, wantOk2)
				} else if wantOk2 {
					if ans[i].K2 != kvs2[ki] {
						t.Errorf("got %v for v2.k2 %d but expected %v", ans[i].K2, i, kvs2[ki])
					}
					if ans[i].V2 != kvs2[vi] {
						t.Errorf("got %v for v2.v2 %d but expected %v", ans[i].V2, i, kvs2[vi])
					}
				}
			}
		}
	})
}

func TestZip2(t *testing.T) {
	testCases := []struct {
		name string
		s1   Seq2[string, int]
		s2   Seq2[string, int]
		want []Zipped2[string, int, string, int]
	}{
		{
			"equal length",
			OfKVs[string, int]("foo", 1, "bar", 2),
			OfKVs[string, int]("baz", 3, "qux", 4),
			[]Zipped2[string, int, string, int]{
				{K1: "foo", V1: 1, Ok1: true, K2: "baz", V2: 3, Ok2: true},
				{K1: "bar", V1: 2, Ok1: true, K2: "qux", V2: 4, Ok2: true},
			},
		},
		{
			"non-equal length",
			OfKVs[string, int]("foo", 1),
			OfKVs[string, int]("baz", 3, "qux", 4),
			[]Zipped2[string, int, string, int]{
				{K1: "foo", V1: 1, Ok1: true, K2: "baz", V2: 3, Ok2: true},
				{K2: "qux", V2: 4, Ok2: true},
			},
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := ToSlice(Zip2(tc.s1, tc.s2))
			if !slices.Equal(ans, tc.want) {
				t.Errorf("got %v, expected %v", ans, tc.want)
			}
		})
	}
}

func TestEqual0(t *testing.T) {
	testCases := []struct {
		name   string
		n1, n2 int
		want   bool
	}{
		{"both empty", 0, 0, true},
		{"equal length", 4, 4, true},
		{"non-equal length", 2, 4, false},
		{"non-equal length", 4, 2, false},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			s1 := MkSeq0(new(int), tc.n1)
			s2 := MkSeq0(new(int), tc.n2)
			ans := Equal0(s1, s2)
			if ans != tc.want {
				t.Errorf("got %t, expected %t", ans, tc.want)
			}
		})
	}
}

func TestEqual(t *testing.T) {
	testCases := []struct {
		name string
		s1   []int
		s2   []int
		want bool
	}{
		{"Equal", []int{1, 2}, []int{1, 2}, true},
		{"Empty equal", nil, nil, true},
		{"Not Equal", []int{1, 2}, []int{1, 3}, false},
		{"Different size", []int{1}, []int{1, 2}, false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := Equal(OfSlice(tc.s1), OfSlice(tc.s2))
			if ans != tc.want {
				t.Errorf("got %t, want %t (%v - %v)", ans, tc.want, tc.s1, tc.s2)
			}
		})
	}
}

func TestEqual2(t *testing.T) {
	testCases := []struct {
		name   string
		s1, s2 Seq2[string, int]
		want   bool
	}{
		{"Equal", OfKVs[string, int]("foo", 1), OfKVs[string, int]("foo", 1), true},
		{"Empty equal", Empty2[string, int](), Empty2[string, int](), true},
		{"Equal", OfKVs[string, int]("foo", 1), OfKVs[string, int]("bar", 1), false},
		{"Different size", OfKVs[string, int]("foo", 1), OfKVs[string, int](), false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := Equal2(tc.s1, tc.s2)
			if ans != tc.want {
				t.Errorf("got %t, want %t", ans, tc.want)
			}
		})
	}
}

func TestEqualFunc(t *testing.T) {
	testCases := []struct {
		name   string
		s1, s2 Seq[int]
		f      func(int, int) bool
		want   bool
	}{
		{
			"equal",
			Of(1, 2),
			Of(2, 4),
			func(i1, i2 int) bool {
				return i1*2 == i2
			},
			true,
		},
		{
			"not equal",
			Of(1, 2),
			Of(2, 4),
			func(i1, i2 int) bool {
				return i1 == i2
			},
			false,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := EqualFunc(tc.s1, tc.s2, tc.f)
			if ans != tc.want {
				t.Errorf("got %t, expected %t", ans, tc.want)
			}
		})
	}
}

func TestEqualFunc2(t *testing.T) {
	testCases := []struct {
		name   string
		s1, s2 Seq2[int, int]
		f      func(int, int, int, int) bool
		want   bool
	}{
		{
			"equal",
			OfKVs[int, int](1, 2),
			OfKVs[int, int](2, 8),
			func(k1, v1, k2, v2 int) bool {
				return k1*2 == k2 && v1*4 == v2
			},
			true,
		},
		{
			"not equal",
			OfKVs[int, int](1, 2),
			OfKVs[int, int](2, 8),
			func(k1, v1, k2, v2 int) bool {
				return k1 == k2 && v1 == v2
			},
			false,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := EqualFunc2(tc.s1, tc.s2, tc.f)
			if ans != tc.want {
				t.Errorf("got %t, expected %t", ans, tc.want)
			}
		})
	}
}

func FuzzForeach(f *testing.F) {
	testCases := []int{0, 1, 3}
	for _, tc := range testCases {
		f.Add(tc)
	}

	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)
		s := MkRandSlice(n)

		var ans []int
		Foreach(func(i int) {
			ans = append(ans, i)
		}, OfSlice(s))

		if !slices.Equal(ans, s) {
			t.Errorf("got %v, expected %v", ans, s)
		}
	})
}

func FuzzForeach2(f *testing.F) {
	testCases := []int{0, 1, 3}
	for _, tc := range testCases {
		f.Add(tc)
	}

	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)
		s := MkRandKVSlice(n)

		var ans []any
		Foreach2(func(k, v int) {
			ans = append(ans, k, v)
		}, OfKVSlice[int, int](s))

		if !slices.Equal(ans, s) {
			t.Errorf("got %v, expected %v", ans, s)
		}
	})
}

func TestTap(t *testing.T) {
	var got []int
	Drain(Tap(func(v int) {
		got = append(got, v)
	}, Take(2, Of(1, 2, 3))))

	want := []int{1, 2}
	if !slices.Equal(got, want) {
		t.Errorf("got %v, expected %v", got, want)
	}
}

func TestTap2(t *testing.T) {
	var got []any
	Drain2(Tap2(func(k, v int) {
		got = append(got, k, v)
	}, Take2(2, OfKVs[int, int](1, 2, 3, 4, 5, 6))))

	want := []any{1, 2, 3, 4}
	if !slices.Equal(got, want) {
		t.Errorf("got %v, expected %v", got, want)
	}
}

func TestFilter(t *testing.T) {
	got := ToSlice(Filter(func(i int) bool { return i%2 == 0 }, Of(1, 2, 3, 4, 5, 6)))
	want := []int{2, 4, 6}

	if !slices.Equal(got, want) {
		t.Errorf("got %v, expected %v", got, want)
	}
}

func TestFilter2(t *testing.T) {
	got := ToKVSlice(Filter2(func(k string, v int) bool {
		return len(k)%2 == 0 && v%2 == 0
	}, OfKVs[string, int]("f", 1, "fo", 2, "foo", 3)))
	want := []any{"fo", 2}

	if !slices.Equal(got, want) {
		t.Errorf("got %v, expected %v", got, want)
	}
}

func TestFilterNotEqual(t *testing.T) {
	got := ToSlice(FilterNotEqual(4, Of(1, 2, 3, 4, 5, 6)))
	want := []int{1, 2, 3, 5, 6}

	if !slices.Equal(got, want) {
		t.Errorf("got %v, expected %v", got, want)
	}
}

func TestFilterNotEqual2(t *testing.T) {
	got := ToKVSlice(FilterNotEqual2("bar", 2, OfKVs[string, int]("foo", 1, "bar", 2, "baz", 3)))
	want := []any{"foo", 1, "baz", 3}

	if !slices.Equal(got, want) {
		t.Errorf("got %v, expected %v", got, want)
	}
}

func TestFind(t *testing.T) {
	testCases := []struct {
		name string
		seq  []int
		v    int
		want bool
	}{
		{"present", []int{1, 2, 3, 4}, 2, true},
		{"not present", []int{1, 2, 3, 4}, 5, false},
		{"empty", []int{}, 2, false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			v, ans := Find(func(v int) bool {
				return v == tc.v
			}, OfSlice(tc.seq))

			if ans != tc.want {
				t.Errorf("got %t, expected %t (%v in %v)", ans, tc.want, tc.v, tc.seq)
			} else if ans && v != tc.v {
				t.Errorf("got %v, expected %v", v, tc.v)
			}
		})
	}
}

func TestFind2(t *testing.T) {
	testCases := []struct {
		name string
		seq  []any
		k    int
		v    string
		want bool
	}{
		{"present", []any{1, "foo", 2, "bar", 3, "baz", 4, "qux"}, 2, "bar", true},
		{"not present", []any{1, "foo", 2, "bar", 3, "baz", 4, "qux"}, 5, "bang", false},
		{"empty", []any{}, 2, "bar", false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			k, v, ans := Find2(func(k int, v string) bool {
				return k == tc.k && v == tc.v
			}, OfKVSlice[int, string](tc.seq))

			if ans != tc.want {
				t.Errorf("got %t, expected %t (%v in %v)", ans, tc.want, tc.v, tc.seq)
			} else if ans {
				if k != tc.k {
					t.Errorf("got k %v, expected k %v", k, tc.k)
				}
				if v != tc.v {
					t.Errorf("got v %v, expected v %v", v, tc.v)
				}
			}
		})
	}
}

func TestContains(t *testing.T) {
	testCases := []struct {
		name string
		seq  []int
		v    int
		want bool
	}{
		{"present", []int{1, 2, 3, 4}, 2, true},
		{"not present", []int{1, 2, 3, 4}, 5, false},
		{"empty", []int{}, 2, false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := Contains(OfSlice(tc.seq), tc.v)

			if ans != tc.want {
				t.Errorf("got %t, expected %t (%v in %v)", ans, tc.want, tc.v, tc.seq)
			}
		})
	}
}

func TestContains2(t *testing.T) {
	testCases := []struct {
		name string
		seq  []any
		k    int
		v    string
		want bool
	}{
		{"present", []any{1, "foo", 2, "bar", 3, "baz", 4, "qux"}, 2, "bar", true},
		{"not present", []any{1, "foo", 2, "bar", 3, "baz", 4, "qux"}, 5, "bang", false},
		{"empty", []any{}, 2, "bar", false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := Contains2(OfKVSlice[int, string](tc.seq), tc.k, tc.v)

			if ans != tc.want {
				t.Errorf("got %t, expected %t (%v in %v)", ans, tc.want, tc.v, tc.seq)
			}
		})
	}
}

func TestContainsFunc(t *testing.T) {
	testCases := []struct {
		name string
		seq  []int
		v    int
		want bool
	}{
		{"present", []int{1, 2, 3, 4}, 2, true},
		{"not present", []int{1, 2, 3, 4}, 5, false},
		{"empty", []int{}, 2, false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := ContainsFunc(func(v int) bool {
				return v == tc.v
			}, OfSlice(tc.seq))

			if ans != tc.want {
				t.Errorf("got %t, expected %t (%v in %v)", ans, tc.want, tc.v, tc.seq)
			}
		})
	}
}

func TestContainsFunc2(t *testing.T) {
	testCases := []struct {
		name string
		seq  []any
		k    int
		v    string
		want bool
	}{
		{"present", []any{1, "foo", 2, "bar", 3, "baz", 4, "qux"}, 2, "bar", true},
		{"not present", []any{1, "foo", 2, "bar", 3, "baz", 4, "qux"}, 5, "bang", false},
		{"empty", []any{}, 2, "bar", false},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := ContainsFunc2(func(k int, v string) bool {
				return k == tc.k && v == tc.v
			}, OfKVSlice[int, string](tc.seq))

			if ans != tc.want {
				t.Errorf("got %t, expected %t (%v in %v)", ans, tc.want, tc.v, tc.seq)
			}
		})
	}
}

func FuzzTake0(f *testing.F) {
	testCases := []int{
		0, 1, 3, 5,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}
	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)
		var l int
		if n > 0 {
			l = rand.Intn(n)
		}

		var calls int
		seq := MkSeq0(&calls, n)

		Drain0(Take0(l, seq))

		if calls != l {
			t.Errorf("got %d calls, expected %d", calls, l)
		}
	})
}

func FuzzTake(f *testing.F) {
	testCases := []int{
		0, 1, 3, 5,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}
	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)

		var l int
		if n > 0 {
			l = rand.Intn(n)
		}
		seq := MkRandSlice(n)

		ans := ToSlice(Take(l, OfSlice(seq)))
		want := seq[:l]

		if !slices.Equal(ans, want) {
			t.Errorf("got %v, expected %v", ans, want)
		}
	})
}

func FuzzTake2(f *testing.F) {
	testCases := []int{
		0, 1, 3, 5,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}
	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)

		var l int
		if n > 0 {
			l = rand.Intn(n)
		}
		seq := MkRandKVSlice(n)

		ans := ToKVSlice(Take2(l, OfKVSlice[int, int](seq)))
		want := seq[:l*2]

		if !slices.Equal(ans, want) {
			t.Errorf("got %v, expected %v", ans, want)
		}
	})
}

func TestTakeWhile(t *testing.T) {
	tests := []struct {
		name     string
		f        func(int) bool
		seq      Seq[int]
		expected Seq[int]
	}{
		{
			name:     "Empty sequence",
			f:        func(n int) bool { return n < 5 },
			seq:      Of[int](),
			expected: Of[int](),
		},
		{
			name:     "All elements are taken",
			f:        func(n int) bool { return n < 5 },
			seq:      Of(1, 2, 3, 4),
			expected: Of(1, 2, 3, 4),
		},
		{
			name:     "Some elements are taken",
			f:        func(n int) bool { return n < 5 },
			seq:      Of(1, 2, 3, 4, 5, 6, 7),
			expected: Of(1, 2, 3, 4),
		},
		{
			name:     "No elements are taken",
			f:        func(n int) bool { return n < 0 },
			seq:      Of(1, 2, 3, 4, 5, 6, 7),
			expected: Of[int](),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := TakeWhile(tt.f, tt.seq)
			if ok := Equal[int](result, tt.expected); !ok {
				t.Errorf("Got different sequence than expected for %s", tt.name)
			}
		})
	}
}

func TestTakeWhile2(t *testing.T) {
	tests := []struct {
		name     string
		f        func(string, int) bool
		seq      Seq2[string, int]
		expected Seq2[string, int]
	}{
		{
			name:     "Empty sequence",
			f:        func(_ string, n int) bool { return n < 5 },
			seq:      OfKVs[string, int](),
			expected: OfKVs[string, int](),
		},
		{
			name:     "All elements are taken",
			f:        func(_ string, n int) bool { return n < 5 },
			seq:      OfKVs[string, int]("foo", 1, "bar", 2, "baz", 3, "qux", 4),
			expected: OfKVs[string, int]("foo", 1, "bar", 2, "baz", 3, "qux", 4),
		},
		{
			name:     "Some elements are taken",
			f:        func(_ string, n int) bool { return n < 5 },
			seq:      OfKVs[string, int]("a", 1, "b", 2, "c", 3, "d", 4, "e", 5, "f", 6, "g", 7),
			expected: OfKVs[string, int]("a", 1, "b", 2, "c", 3, "d", 4),
		},
		{
			name:     "No elements are taken",
			f:        func(_ string, n int) bool { return n < 0 },
			seq:      OfKVs[string, int]("a", 1, "b", 2, "c", 3, "d", 4, "e", 5, "f", 6, "g", 7),
			expected: OfKVs[string, int](),
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := TakeWhile2(tt.f, tt.seq)
			if ok := Equal2[string, int](result, tt.expected); !ok {
				t.Errorf("Got different sequence than expected for %s", tt.name)
			}
		})
	}
}

func TestDrop(t *testing.T) {
	tests := []struct {
		name    string
		n       int
		seq     []int
		wantSeq []int
	}{
		{
			name:    "DropFirstThree",
			n:       3,
			seq:     []int{1, 2, 3, 4, 5, 6},
			wantSeq: []int{4, 5, 6},
		},
		{
			name:    "SeqLessThanN",
			n:       7,
			seq:     []int{1, 2, 3, 4, 5, 6},
			wantSeq: []int{},
		},
		{
			name:    "EmptySeq",
			n:       3,
			seq:     []int{},
			wantSeq: []int{},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ans := ToSlice(Drop(tt.n, OfSlice(tt.seq)))
			want := tt.wantSeq
			if !slices.Equal(ans, want) {
				t.Errorf("got %v, want %v", ans, want)
			}
		})
	}
}

func TestDrop2(t *testing.T) {
	tests := []struct {
		name    string
		n       int
		seq     []any
		wantSeq []any
	}{
		{
			name:    "DropFirstThree",
			n:       3,
			seq:     []any{"a", 1, "b", 2, "c", 3, "d", 4, "e", 5, "f", 6},
			wantSeq: []any{"d", 4, "e", 5, "f", 6},
		},
		{
			name:    "SeqLessThanN",
			n:       7,
			seq:     []any{"a", 1, "b", 2, "c", 3, "d", 4, "e", 5, "f", 6},
			wantSeq: []any{},
		},
		{
			name:    "EmptySeq",
			n:       3,
			seq:     []any{},
			wantSeq: []any{},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			ans := ToKVSlice[string, int](Drop2[string, int](tt.n, OfKVSlice[string, int](tt.seq)))
			want := tt.wantSeq
			if !slices.Equal(ans, want) {
				t.Errorf("got %v, want %v", ans, want)
			}
		})
	}
}

func TestDropWhile(t *testing.T) {
	testCases := []struct {
		name string
		f    func(int) bool
		seq  []int
		want []int
	}{
		{
			"empty seq",
			func(i int) bool { return i < 3 },
			[]int{},
			[]int{},
		},
		{
			"drop some",
			func(i int) bool { return i < 3 },
			[]int{1, 2, 3, 4, 5},
			[]int{3, 4, 5},
		},
		{
			"drop all",
			func(i int) bool { return i < 6 },
			[]int{1, 2, 3, 4, 5},
			[]int{},
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := ToSlice(DropWhile(tc.f, OfSlice(tc.seq)))
			want := tc.want
			if !slices.Equal(ans, want) {
				t.Errorf("got %v, want %v", ans, want)
			}
		})
	}
}

func TestDropWhile2(t *testing.T) {
	testCases := []struct {
		name string
		f    func(string, int) bool
		seq  []any
		want []any
	}{
		{
			"empty seq",
			func(_ string, i int) bool { return i < 3 },
			[]any{},
			[]any{},
		},
		{
			"drop some",
			func(_ string, i int) bool { return i < 3 },
			[]any{"a", 1, "b", 2, "c", 3, "d", 4, "e", 5},
			[]any{"c", 3, "d", 4, "e", 5},
		},
		{
			"drop all",
			func(_ string, i int) bool { return i < 6 },
			[]any{"a", 1, "b", 2, "c", 3, "d", 4, "e", 5},
			[]any{},
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := ToKVSlice(DropWhile2(tc.f, OfKVSlice[string, int](tc.seq)))
			want := tc.want
			if !slices.Equal(ans, want) {
				t.Errorf("got %v, want %v", ans, want)
			}
		})
	}
}

func TestGrouped(t *testing.T) {
	testCases := []struct {
		name string
		n    int
		seq  []int
		want [][]int
	}{
		{
			"empty seq",
			2,
			[]int{},
			nil,
		},
		{
			"single elem",
			2,
			[]int{1},
			[][]int{{1}},
		},
		{
			"multi elem",
			2,
			[]int{1, 2},
			[][]int{{1, 2}},
		},
		{
			"multi multi elem",
			2,
			[]int{1, 2, 3, 4, 5},
			[][]int{{1, 2}, {3, 4}, {5}},
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := ToSlice(Grouped(tc.n, OfSlice(tc.seq)))
			want := tc.want
			if !reflect.DeepEqual(ans, want) {
				t.Errorf("got %v, want %v", ans, want)
			}
		})
	}
}

func TestMap(t *testing.T) {
	seq := []int{1, 2, 3, 4}
	ans := ToSlice(Map(func(i int) int { return i * i }, OfSlice(seq)))
	want := []int{1, 4, 9, 16}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestMap2(t *testing.T) {
	seq := []any{"a", 1, "b", 2, "c", 3, "d", 4}
	ans := ToKVSlice(Map2(func(s string, i int) (string, int) { return s, i * i }, OfKVSlice[string, int](seq)))
	want := []any{"a", 1, "b", 4, "c", 9, "d", 16}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestFlatmap(t *testing.T) {
	seq := []int{1, 2, 3, 4}
	ans := ToSlice(Flatmap(func(i int) Seq[int] {
		return Of(i, i*i)
	}, OfSlice(seq)))
	want := []int{1, 1, 2, 4, 3, 9, 4, 16}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestFlatmap2(t *testing.T) {
	seq := []any{"a", 1, "b", 2, "c", 3, "d", 4}
	ans := ToKVSlice(Flatmap2(func(s string, i int) Seq2[string, int] {
		return OfKVs[string, int](s, i*i)
	}, OfKVSlice[string, int](seq)))
	want := []any{"a", 1, "b", 4, "c", 9, "d", 16}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestFlatten(t *testing.T) {
	seq := []Seq[int]{Of(1, 2), Of(3, 4)}
	ans := ToSlice(Flatten(OfSlice(seq)))
	want := []int{1, 2, 3, 4}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestFlatten2(t *testing.T) {
	seq := []Seq2[int, int]{OfKVs[int, int](1, 2), OfKVs[int, int](3, 4)}
	ans := ToKVSlice(Flatten2(OfSlice(seq)))
	want := []any{1, 2, 3, 4}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestReduce(t *testing.T) {
	ans := Reduce(0, func(s, v int) int { return s + v }, Of(1, 2, 3, 4, 5))
	want := 15
	if ans != want {
		t.Errorf("got %d, expected %d", ans, want)
	}
}

func TestReduce2(t *testing.T) {
	ans := Reduce2(0, func(s, k, v int) int { return s + k + v }, OfKVs[int, int](1, 2, 3, 4, 5, 6))
	want := 21
	if ans != want {
		t.Errorf("got %d, expected %d", ans, want)
	}
}

func TestKeys(t *testing.T) {
	ans := ToSlice(Keys(OfKVs[string, int]("a", 1, "b", 2, "c", 3)))
	want := []string{"a", "b", "c"}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestValues(t *testing.T) {
	ans := ToSlice(Values(OfKVs[string, int]("a", 1, "b", 2, "c", 3)))
	want := []int{1, 2, 3}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestMapLift(t *testing.T) {
	ans := ToKVSlice(MapLift(func(i int) (string, int) {
		return strconv.Itoa(i), i
	}, Of(1, 2, 3)))
	want := []any{"1", 1, "2", 2, "3", 3}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestMapLower(t *testing.T) {
	ans := ToSlice(MapLower(func(s string, i int) int {
		return len(s) + i
	}, OfKVs[string, int]("a", 1, "bb", 2, "ccc", 3)))
	want := []int{2, 4, 6}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestMapErr(t *testing.T) {
	ans := ToKVSlice(MapErr(strconv.Atoi, Of("1", "2", "3")))
	want := []any{1, (error)(nil), 2, (error)(nil), 3, (error)(nil)}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestSwap(t *testing.T) {
	ans := ToKVSlice(Swap(OfKVs[string, int]("a", 1, "b", 2, "c", 3)))
	want := []any{1, "a", 2, "b", 3, "c"}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestMapKeys(t *testing.T) {
	ans := ToKVSlice(MapKeys(func(s string) string { return s + s }, OfKVs[string, int]("a", 1, "b", 2, "c", 3)))
	want := []any{"aa", 1, "bb", 2, "cc", 3}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestMapValues(t *testing.T) {
	ans := ToKVSlice(MapValues(func(i int) int { return i + i }, OfKVs[string, int]("a", 1, "b", 2, "c", 3)))
	want := []any{"a", 2, "b", 4, "c", 6}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestRepeat(t *testing.T) {
	ans := ToSlice(Repeat(1, 5))
	want := []int{1, 1, 1, 1, 1}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestRepeat2(t *testing.T) {
	ans := ToKVSlice(Repeat2("a", 1, 3))
	want := []any{"a", 1, "a", 1, "a", 1}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestCache(t *testing.T) {
	seq := Cache(Of(1, 2))
	want := []int{1, 2}

	ans := ToSlice(seq)
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}

	ans = ToSlice(seq)
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestCycle(t *testing.T) {
	ans := ToSlice(Take(5, Cycle(Of(1, 2))))
	want := []int{1, 2, 1, 2, 1}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestCycle2(t *testing.T) {
	ans := ToKVSlice(Take2(5, Cycle2(OfKVs[string, int]("a", 1, "b", 2))))
	want := []any{"a", 1, "b", 2, "a", 1, "b", 2, "a", 1}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestEnumerate(t *testing.T) {
	ans := ToKVSlice(Enumerate(Of("a", "b", "c")))
	want := []any{0, "a", 1, "b", 2, "c"}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestAll(t *testing.T) {
	testCases := []struct {
		name string
		f    func(int) bool
		seq  []int
		want bool
	}{
		{
			"empty seq",
			func(i int) bool { return false },
			[]int{},
			true,
		},
		{
			"matching seq",
			func(i int) bool { return i%2 == 0 },
			[]int{2, 4, 6},
			true,
		},
		{
			"not matching seq",
			func(i int) bool { return i%2 == 0 },
			[]int{2, 4, 5, 6},
			false,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := All(tc.f, OfSlice(tc.seq))
			want := tc.want
			if ans != want {
				t.Errorf("got %t, expected %t", ans, want)
			}
		})
	}
}

func TestAll2(t *testing.T) {
	testCases := []struct {
		name string
		f    func(string, int) bool
		seq  []any
		want bool
	}{
		{
			"empty seq",
			func(s string, i int) bool { return false },
			[]any{},
			true,
		},
		{
			"matching seq",
			func(s string, i int) bool { return i%2 == 0 },
			[]any{"a", 2, "b", 4, "c", 6},
			true,
		},
		{
			"not matching seq",
			func(s string, i int) bool { return i%2 == 0 },
			[]any{"a", 2, "b", 4, "c", 5, "d", 6},
			false,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := All2(tc.f, OfKVSlice[string, int](tc.seq))
			want := tc.want
			if ans != want {
				t.Errorf("got %t, expected %t", ans, want)
			}
		})
	}
}

func TestAny(t *testing.T) {
	testCases := []struct {
		name string
		f    func(int) bool
		seq  []int
		want bool
	}{
		{
			"empty seq",
			func(i int) bool { return true },
			[]int{},
			false,
		},
		{
			"matching seq",
			func(i int) bool { return i%2 == 0 },
			[]int{3, 5, 6},
			true,
		},
		{
			"not matching seq",
			func(i int) bool { return i%2 == 0 },
			[]int{3, 5, 7},
			false,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := Any(tc.f, OfSlice(tc.seq))
			want := tc.want
			if ans != want {
				t.Errorf("got %t, expected %t", ans, want)
			}
		})
	}
}

func TestAny2(t *testing.T) {
	testCases := []struct {
		name string
		f    func(string, int) bool
		seq  []any
		want bool
	}{
		{
			"empty seq",
			func(s string, i int) bool { return true },
			[]any{},
			false,
		},
		{
			"matching seq",
			func(s string, i int) bool { return i%2 == 0 },
			[]any{"a", 3, "b", 5, "c", 6},
			true,
		},
		{
			"not matching seq",
			func(s string, i int) bool { return i%2 == 0 },
			[]any{"a", 3, "b", 5, "c", 7},
			false,
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			ans := Any2(tc.f, OfKVSlice[string, int](tc.seq))
			want := tc.want
			if ans != want {
				t.Errorf("got %t, expected %t", ans, want)
			}
		})
	}
}

func TestCount(t *testing.T) {
	ans := Count(func(i int) bool { return i%2 == 0 }, Of(1, 2, 3, 4, 5))
	want := 2
	if ans != want {
		t.Errorf("got %d, want %d", ans, want)
	}
}

func TestCount2(t *testing.T) {
	ans := Count2(func(s string, i int) bool { return i%2 == 0 }, OfKVs[string, int]("a", 1, "b", 2, "c", 3, "d", 4, "e", 5))
	want := 2
	if ans != want {
		t.Errorf("got %d, want %d", ans, want)
	}
}

func FuzzLen0(f *testing.F) {
	testCases := []int{
		0, 1, 3, 5,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}
	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)
		seq := MkSeq0(new(int), n)
		ans := Len0(seq)
		if ans != n {
			t.Errorf("got %d, expected %d", ans, n)
		}
	})
}

func FuzzLen(f *testing.F) {
	testCases := []int{
		0, 1, 3, 5,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}
	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)
		seq := MkRandSeq(n)
		ans := Len(seq)
		if ans != n {
			t.Errorf("got %d, expected %d", ans, n)
		}
	})
}

func FuzzLen2(f *testing.F) {
	testCases := []int{
		0, 1, 3, 5,
	}
	for _, tc := range testCases {
		f.Add(tc)
	}
	f.Fuzz(func(t *testing.T, n int) {
		n = AbsMod(n, 20)
		seq := MkRandSeq2(n)
		ans := Len2(seq)
		if ans != n {
			t.Errorf("got %d, expected %d", ans, n)
		}
	})
}

func TestIndex(t *testing.T) {
	testCases := []struct {
		name  string
		seq   []int
		idx   int
		want  int
		panic bool
	}{
		{"valid index", []int{1, 2, 3}, 1, 2, false},
		{"invalid index", []int{1, 2, 3}, -1, 0, true},
		{"index out of range", []int{1, 2, 3}, 3, 0, true},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			defer func() {
				v := recover()

				ansPanic := v != nil
				wantPanic := tc.panic

				if ansPanic != wantPanic {
					t.Errorf("got %t panic, expected %t panic", ansPanic, wantPanic)
				}
			}()

			ans := Index(tc.idx, OfSlice(tc.seq))
			if ans != tc.want {
				t.Errorf("got %d, expected %d", ans, tc.want)
			}
		})
	}
}

func TestIndex2(t *testing.T) {
	testCases := []struct {
		name  string
		seq   []any
		idx   int
		wantK int
		wantV int
		panic bool
	}{
		{"valid index", []any{1, 1, 2, 2, 3, 3}, 1, 2, 2, false},
		{"invalid index", []any{1, 1, 2, 2, 3, 3}, -1, 0, 0, true},
		{"index out of range", []any{1, 1, 2, 2, 3, 3}, 3, 0, 0, true},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			defer func() {
				v := recover()

				ansPanic := v != nil
				wantPanic := tc.panic

				if ansPanic != wantPanic {
					t.Errorf("got %t panic, expected %t panic (%v)", ansPanic, wantPanic, v)
				}
			}()

			kAns, vAns := Index2(tc.idx, OfKVSlice[int, int](tc.seq))
			if kAns != tc.wantK {
				t.Errorf("got %d, expected %d", kAns, tc.wantK)
			}
			if vAns != tc.wantV {
				t.Errorf("got %d, expected %d", vAns, tc.wantV)
			}
		})
	}
}

func TestOf(t *testing.T) {
	ans := ToSlice(Of(1, 2, 3))
	want := []int{1, 2, 3}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfSlice(t *testing.T) {
	ans := ToSlice(OfSlice([]int{1, 2, 3}))
	want := []int{1, 2, 3}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfKVs(t *testing.T) {
	ans := ToKVSlice(OfKVs[int, int](1, 2, 3, 4, 5, 6))
	want := []any{1, 2, 3, 4, 5, 6}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfKVSlice(t *testing.T) {
	ans := ToKVSlice(OfKVSlice[int, int]([]any{1, 2, 3, 4, 5, 6}))
	want := []any{1, 2, 3, 4, 5, 6}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfMap(t *testing.T) {
	ans := ToKVSlice(OfMap(map[int]int{1: 2, 2: 3, 3: 4}))
	want := []any{1, 2, 2, 3, 3, 4}
	if !EqualIgnoreOrder(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfMapKeys(t *testing.T) {
	ans := ToSlice(OfMapKeys(map[int]int{1: 2, 2: 3, 3: 4}))
	want := []int{1, 2, 3}
	if !EqualIgnoreOrder(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfMapValues(t *testing.T) {
	ans := ToSlice(OfMapValues(map[int]int{1: 2, 2: 3, 3: 4}))
	want := []int{2, 3, 4}
	if !EqualIgnoreOrder(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfSliceIndex(t *testing.T) {
	ans := ToKVSlice(OfSliceIndex([]int{4, 5, 6}))
	want := []any{0, 4, 1, 5, 2, 6}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfChan(t *testing.T) {
	want := []int{1, 2, 3, 4}

	c := make(chan int, len(want))
	go func() {
		defer close(c)
		for _, i := range want {
			c <- i
		}
	}()

	ans := ToSlice(OfChan(c))
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfNext(t *testing.T) {
	want := []int{1, 2, 3, 4}
	var i int
	ans := ToSlice(OfNext(func() (int, bool) {
		if i >= len(want) {
			return 0, false
		}
		n := want[i]
		i++
		return n, true
	}))
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestOfNext2(t *testing.T) {
	want := []any{1, 1, 2, 4, 3, 9, 4, 16}
	var i int
	ans := ToKVSlice(OfNext2(func() (int, int, bool) {
		if i >= len(want) {
			return 0, 0, false
		}
		n1 := want[i].(int)
		n2 := want[i+1].(int)
		i += 2
		return n1, n2, true
	}))
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestEmpty0(t *testing.T) {
	if Len0(Empty0()) != 0 {
		t.Errorf("Empty0 not empty")
	}
}

func TestEmpty(t *testing.T) {
	if Len(Empty[int]()) != 0 {
		t.Errorf("Empty not empty")
	}
}

func TestEmpty2(t *testing.T) {
	if Len2(Empty2[int, int]()) != 0 {
		t.Errorf("Empty not empty")
	}
}

func TestReceive(t *testing.T) {
	seq := []int{1, 2, 3, 4}
	want := seq[:3]
	c := make(chan int)
	defer close(c)

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	go func() {
		for _, i := range seq {
			c <- i
			if i == len(want) {
				cancel()
				return
			}
		}
	}()
	ans := ToSlice(Receive(ctx, c))
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestCopyToSlice(t *testing.T) {
	ans := make([]int, 3)
	CopyToSlice(ans, Of(1, 2))

	want := []int{1, 2, 0}
	if !slices.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestSetMap(t *testing.T) {
	ans := map[string]int{"c": 3}
	SetMap(ans, OfKVs[string, int]("a", 1, "b", 2))
	want := map[string]int{"a": 1, "b": 2, "c": 3}
	if !maps.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestToMap(t *testing.T) {
	ans := ToMap(OfKVs[string, int]("a", 1, "b", 2))
	want := map[string]int{"a": 1, "b": 2}
	if !maps.Equal(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestAppendSliceMap(t *testing.T) {
	ans := map[string][]int{"c": {3}}
	AppendSliceMap(ans, OfKVs[string, int]("a", 1, "b", 2, "c", 3))
	want := map[string][]int{"a": {1}, "b": {2}, "c": {3, 3}}
	if !reflect.DeepEqual(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}

func TestToSliceMap(t *testing.T) {
	ans := ToSliceMap(OfKVs[string, int]("a", 1, "b", 2, "c", 3, "c", 3))
	want := map[string][]int{"a": {1}, "b": {2}, "c": {3, 3}}
	if !reflect.DeepEqual(ans, want) {
		t.Errorf("got %v, expected %v", ans, want)
	}
}
