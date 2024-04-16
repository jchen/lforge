import Lforge

sig IntArray {
    -- Coe from pfunc to the thing
    elements: pfunc Int -> Int,
    lastIndex: one Int
}
pred validArray[ar: IntArray] {
    -- We can make these more efficient

    -- no elements before index 0
    all i: Int | i < 0 implies no ar.elements[i]
    -- if there's an element, either i=0 or there's something at i=1
    -- also the array is sorted:
    all i: Int | some ar.elements[i] implies {
        i = 0 or some ar.elements[subtract[i, 1]] and
        ar.elements[i] /* as Int */ >= ar.elements[subtract[i, 1]]
    }
    -- size variable reflects actual size of array
    all i: Int | (no ar.elements[i] and some ar.elements[subtract[i, 1]]) implies {
        ar.lastIndex = subtract[i, 1]
    }
    {all i: Int | no ar.elements[i]} implies
      {ar.lastIndex = -1}

}

fun firstIndex[arr: IntArray]: one Int {
    -- We cannot write this in Froglet
    --no arr.elements   => -1
    -- But we can write this:
    if arr.lastIndex = -1  then -1
                      else  0
}

sig SearchState {
    arr: one IntArray,
    low: one Int,
    high: one Int,
    target: one Int
}

pred init[s: SearchState] {
    validArray[s.arr]
    s.low = firstIndex[s.arr]
    s.high = s.arr.lastIndex
    -- no constraints on the target; may search for any value
}

pred stepNarrow[pre: SearchState, post: SearchState] {
    -- mid = (low+high)/2  (rounded down)
    let mid = divide[add[pre.low, pre.high], 2] | {
      -- GUARD: must continue searching, this isn't it
      pre.arr.elements[mid] != pre.target
      -- ACTION: narrow left or right
      pre.arr.elements[mid] < pre.target
          => {
            -- need to go higher
            post.low = add[mid, 1] and
            post.high = pre.high
          }
          else {
            -- need to go lower
            post.low = pre.low and
            post.high = subtract[mid, 1]
          } and
      -- FRAME: these don't change
      post.arr = pre.arr and
      post.target = pre.target
    }
}

pred searchFailed[pre: SearchState] {
    pre.low > pre.high
}
pred searchSucceed[pre: SearchState] {
    let mid = divide[add[pre.low, pre.high], 2] |
        pre.arr.elements[mid] = pre.target
}

-- For trace-based analysis, prevent early deadlock
pred stepDoneFail[pre: SearchState, post: SearchState] {
    -- GUARD: low and high have crossed
    searchFailed[pre]
    -- ACTION: no change
    post.arr = pre.arr
    post.target = pre.target
    post.low = pre.low
    post.high = pre.high
}
pred stepDoneSucceed[pre: SearchState, post: SearchState] {
    -- GUARD: mid = target
    -- Note: bad error message if we leave out .elements and say pre.arr[mid]
    searchSucceed[pre]
    -- ACTION: no change
    post.arr = pre.arr
    post.target = pre.target
    post.low = pre.low
    post.high = pre.high
}

pred anyTransition[pre: SearchState, post: SearchState] {
    stepNarrow[pre, post]      or
    stepDoneFail[pre, post]    or
    stepDoneSucceed[pre, post]
}

-- Binary search (not so) famously breaks if the array is too long, and low+high overflows
-- We can always represent max[Int] (but not #Int; we'd never have enough integers since negatives exist)
pred safeArraySize[arr: IntArray] {
    -- E.g., if lastIndex is 5, there are 6 elements in the array. If the first step takes us from (0, 6) to
    -- (3,6) then (high+low) = 9, which cannot be represented in Forge with 4 bits. We need to prevent that.
    -- (See: https://ai.googleblog.com/2006/06/extra-extra-read-all-about-it-nearly.html)

    -- FILL (Exercise 2--3)
}

-- pred test {
--     -- It's possible to narrow on the first transition (this is the common case)
--     narrowFirstPossible: {
--         some s1,s2: SearchState | {
--             init[s1]
--             safeArraySize[s1.arr]
--             stepNarrow[s1, s2]
--         }
--     } for exactly 1 IntArray, exactly 2 SearchState
--     is sat

--     -- If the first state has the target exactly in the middle, we can succeed immediately
--     doneSucceedFirstPossible: {
--         some s1,s2: SearchState | {
--             init[s1]
--             safeArraySize[s1.arr]
--             stepDoneSucceed[s1, s2]
--         }
--     } for exactly 1 IntArray, exactly 2 SearchState
--     is sat

--     -- Since we start with high >= low, the failure condition can't already be reached
--     doneFailFirstPossible: {
--         some s1,s2: SearchState | {
--             init[s1]
--             safeArraySize[s1.arr]
--             stepDoneFail[s1, s2]
--         }
--     } for exactly 1 IntArray, exactly 2 SearchState
--     is unsat
-- }

pred bsearchInvariant[s: State] {
    -- If the target is present, it's located between low and high
    all i: Int | {
        s.arr.elements[i] = s.target => {
            s.low <= i and
            s.high >= i

            -- FILL (exercise 2--3)
        }
    }
}
