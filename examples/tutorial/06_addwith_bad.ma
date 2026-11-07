-- Tutorial chapter 6: Higher-order and nested data
-- Expect: reject (termination)
-- `addWith` from 06_higher_order.ma, but the function argument is only
-- known to return some number, `SNat #`. The results `f j y` and `f i x`
-- have size `#`, so the recursive call must be made at sizes `#`, and
-- nothing decreases. The termination check rejects it. This is right:
-- with f = (\ k -> \ n -> ssucc # n), the function would never stop.

sized data SNat : Size -> Set
{
  szero : (i : Size) -> SNat ($ i);
  ssucc : (i : Size) -> SNat i -> SNat ($ i)
}

fun addWith : ((k : Size) -> SNat k -> SNat #) ->
              (i : Size) -> (j : Size) -> SNat i -> SNat j -> SNat #
{
  addWith f .($ i) j (szero i)   y = y;
  addWith f .($ i) j (ssucc i x) y = ssucc # (addWith f # # (f j y) (f i x))
}
