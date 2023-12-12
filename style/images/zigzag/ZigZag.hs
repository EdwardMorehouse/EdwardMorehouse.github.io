{-
 -  learning the diagrams package
 -  compile with:
 -  ghc --make ZigZag.hs ; ./ZigZag -o ZigZag.svg -w 1000
 -}

{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

--module ZigZag  where

import  Interlude
import  Data.Monoid.Endomorphism
import  Data.Tree
import  Data.Maybe
import  Control.Monad
import  Diagrams.Prelude
import  Diagrams.Backend.SVG.CmdLine
import  Diagrams.TwoD.Path.Metafont
import  Diagrams.TwoD.Layout.Tree


main = mainWith (diagram # pad 1.1)

math_font  =  "STIX"


emptyDiagram  =  pointDiagram origin

node  =  \ label →
	text label # font math_font
	<>
	roundedRect (fromIntegral $ length label) 1.0 0.5
		# lw 0.025
		# fc white . opacity 0.75

wire  =  \ label →
	text label # font math_font
	<>
	roundedRect (fromIntegral $ length label) 1.0 0.5
		# lc white . opacity 0.98
		# fc white . opacity 0.98

region  =  \ label →
	text label # font math_font

-- nice!
labels  =  map ((uncurry label) ⋅ Endomorphism) ⋅ mconcat ⋅ getEndomorphism
	where
		label n l  =  withName n (location ⋅ place l ⋅ atop)


-- adjunction zig-zag

zigzag  =  (mconcat ∘ mconcat) [two_cells , one_cells , label_anchors , decorations]
	# lw 0.1
	# scale 3
	# pad 1.1
	# labels
		[
			("unit" , node "η") ,
			("counit" , node "ε") 
			--("F1" , wire "F") ,
			--("F2" , wire "F") ,
			--("G" , wire "G" ) ,
			--("A" , region "𝔸" ) ,
			--("B" , region "𝔹" )
		]
	# localize
	where
		boundary  ∷  Located (Trail R2)
		boundary  =  rect 5 4
		-- vectors
		toEnter  =  r2 (2 , 2)
		toCap  =  r2 (-1 , 1)
		-- points
		enter  =  origin .+^ toEnter
		leave  =  origin .-^ toEnter
		cap  =  origin .+^ toCap
		cup  =  origin .-^ toCap
		-- 2-cells
		unit  =  place (emptyDiagram # named "unit") cap
		counit  =  place (emptyDiagram # named "counit") cup
		two_cells  =  [unit , counit]
		-- 1-cells
		curve  ∷  Located (Trail R2)
		curve  =  metafont
			(
				enter
					.- leaving unit_Y <> 1.2 `tensions` 1.1 <> arriving unit_X -.
				cup
					.- leaving unit_X <> 1.0 `tensions` 1.0 <> arriving unit_X -.
				cap
					.- leaving unit_X <> 1.1 `tensions` 1.2 <>  arriving unit_Y -. endpt
				leave
			)
		one_cells  =  map strokeLocTrail [curve]
		-- label anchors
		f1_l  =   place (emptyDiagram # named "F1") (fromMaybe enter (maxTraceP cup unit_X curve))
		g_l  =  place (emptyDiagram # named "G") (curve `atParam` (1/2))
		f2_l  =   place (emptyDiagram # named "F2") (fromMaybe leave (maxTraceP cap unitX curve))
		a_l  =  place (emptyDiagram # named "A")
			(cap .+^ ((2/3) *^ fromMaybe unitY (maxTraceV cap (unitY # rotateBy (1/6)) boundary)))
		b_l  =  place (emptyDiagram # named "B")
			(cup .+^ ((2/3) *^ fromMaybe unit_Y (maxTraceV cup (unit_Y # rotateBy (1/6)) boundary)))
		label_anchors  =  [f1_l , g_l , f2_l , a_l , b_l]
		-- decorations
		decorations  =  [] --map strokeLocTrail [boundary]

---------------

diagram :: Diagram B R2
diagram =
	zigzag # opacity (1/16)
