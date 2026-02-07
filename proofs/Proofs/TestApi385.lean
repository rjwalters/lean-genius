-- Test API availability for erdos-385 (part 2 - minimal filter)
import Mathlib.Order.Filter.AtTopBot

-- Filter APIs
#check Filter.Eventually
#check Filter.Eventually.mono
#check Filter.Tendsto
#check Filter.atTop
#check Filter.eventually_atTop
#check @Filter.tendsto_atTop
