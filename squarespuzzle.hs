
import Data.List
import Data.Maybe
import qualified Data.Set as Set

data Answer = Definite String
            | Unknown String [Char]
            deriving (Eq, Show)

type Ring = ([Answer], Set.Set Answer)
type Rings = ([[Answer]], Set.Set Answer)

append :: Ring -> Ring -> Ring
append (ring1, as1) (ring2, as2) = (ring1 ++ ring2, as1 `mappend` as2)

appendOne :: Ring -> Answer -> Ring
appendOne (ring, as) a = (ring ++ [a], Set.insert a as)

ringIntersect :: Ring -> Ring -> Set.Set Answer
ringIntersect (_, ring1) (_, ring2) = Set.intersection ring1 ring2

ringsIntersect :: Rings -> Rings -> Set.Set Answer
ringsIntersect (_, rings1) (_, rings2) = Set.intersection rings1 rings2

answers = [
            Unknown "1" ['A']
          , Definite "aping"
          , Definite "avast"
          , Definite "banks"
          , Definite "bouts"
          , Definite "chili"
          , Definite "choir"
          , Definite "donor"
          , Definite "elect"
          , Definite "forge"
          , Definite "gourd"
          , Definite "grave"
          , Definite "incus"
          , Definite "levis"
          , Definite "model"
          , Definite "mount"
          , Definite "octet"
          , Definite "orris"
          , Definite "ought"
          , Unknown "2" ['O', 'R']
          , Unknown "3" ['O', 'R']
          , Definite "rapid"
          , Definite "ratal"
          , Definite "recap"
          , Definite "repel"
          , Definite "sappy"
          , Definite "shark"
          , Definite "slick"
          , Definite "smoke"
          , Definite "sport"
          , Definite "tacks"
          , Definite "takar"
          , Definite "tones"
          , Definite "tussy"
          , Definite "video"
          , Definite "virus"
          , Definite "wands"
          , Definite "wring"
          ]

isDefinite (Definite _) = True
isDefinite (Unknown _ _) = False

knownAnswers = filter isDefinite answers

buildRings :: [Answer] -> Ring -> [Ring]
buildRings _ ([], _) = error "Need a start node to build ring"
buildRings _ ring @ ([_, _, _, _], _) = [ring]
buildRings answers l @ ([current], _) =
   let nexts = filter (\ n -> validateLastToFirst current n) answers
       in
       nexts >>= (\ next ->
          buildRings answers (appendOne l next))
buildRings answers l @ ([_, current], _) =
   let nexts = filter (\ n -> validatePair last current last n) answers
       in
       nexts >>= (\ next ->
          buildRings answers (appendOne l next))
buildRings answers l @ ([first, _, current], _) =
   let nexts = filter (\ n ->
                  validateFirstToLast current n
                  && validateFirstToFirst first n) answers
      in
      nexts >>= (\ next ->
         buildRings answers (appendOne l next))

distinct :: Ring -> Bool
distinct (xs, _) = null (filter (\ l -> length l > 1)
                     (map (\ x -> filter (== x) xs) xs))

allRings :: [Ring]
allRings = do
   start <- answers
   let start' = [start]
   ring <- buildRings answers (start', Set.fromList start')
   if distinct ring
      then [ring]
      else []

validAnswer :: [Ring] -> Bool
validAnswer = distinct . concat

nonDistinctPossibleAnswers :: Rings
nonDistinctPossibleAnswers =
   concat . map (\ ring -> getLinkedRings ring allRings) $ allRings

possibleAnswers = filter validAnswer nonDistinctPossibleAnswers

possibleFullAnswers = do
   part1 <- possibleAnswers
   part2 <- filter (null . ringsIntersect p1) possibleAnswers
   return (part1, part2)

getRings :: (Ring -> Ring -> Bool) -> Ring -> [Ring] -> [(Ring, [Ring])]
getRings pred ring rings = do
   other <- rings
   if pred ring other
      then [(other,
            filter (null . ringIntersect other) rings)]
      else []

isTopLeft (ring, _) (other, _) =
   validatePair (!! 3) (other !! 1) (!! 1) (head ring)
   && validatePair (!! 3) (other !! 2) (!! 1) (last ring)

getTopLefts :: Ring -> [Ring] -> [(Ring, [Ring])]
getTopLefts = getRings isTopLeft

isTopRight (ring, _) (other, _) =
   validatePair (!! 3) (last other) (!! 3) (head ring)
   && validatePair (!! 1) (other !! 2) (!! 1) (ring !! 1)

getTopRights :: Ring -> [Ring] -> [(Ring, [Ring])]
getTopRights = getRings isTopRight

isBottomLeft (ring, _) (other, _) =
   validatePair (!! 3) (head other) (!! 3) (last ring)
   && validatePair (!! 1) (other !! 1) (!! 1) (ring !! 2)

getBottomLefts :: Ring -> [Ring] -> [(Ring, [Ring])]
getBottomLefts = getRings isBottomLeft

isBottomRight (ring, _) (other, _) =
   validatePair (!! 1) (head other) (!! 3) (ring !! 1)
   && validatePair (!! 1) (last other) (!! 3) (ring !! 2)

getBottomRights :: Ring -> [Ring] -> [(Ring, [Ring])]
getBottomRights = getRings isBottomRight

getLinkedRings :: Ring -> [Ring] -> Rings
getLinkedRings ring @ (ring', ringAs) rings = do
   let validRings = filter (null . ringIntersect ring) rings
   ((topLeft, topLeftAs), rings') <- getTopLefts ring validRings
   ((topRight, topRightAs), rings'') <- getTopRights ring rings'
   ((bottomLeft, bottomLeftAs), rings''') <- getBottomLefts ring rings''
   ((bottomRight, bottomRightAs), _) <- getBottomRights ring rings'''
   return ([topLeft, topRight, ring', bottomLeft, bottomRight],
           topLeftAs `mappend` topRightAs `mappend` ringAs `mappend` bottomLeftAs `mappend` bottomRightAs)

validatePair word1Accessor (Definite word1) word2Accessor (Definite word2) =
   word1Accessor word1 == word2Accessor word2
validatePair _ _ _ _ = True

validateLastToFirst word1 @ (Definite _) word2 @ (Definite _) = validatePair last word1 head word2
validateLastToFirst (Definite word1) (Unknown _ firsts) = elem (last word1) firsts
validateLastToFirst _ _ = True

validateFirstToLast word1 @ (Definite _) word2 @ (Definite _) = validatePair head word1 last word2
validateFirstToLast (Unknown _ firsts) (Definite word2) = elem (last word2) firsts
validateFirstToLast _ _ = True

validateFirstToFirst word1 @ (Definite _) word2 @ (Definite _) = validatePair head word1 head word2
validateFirstToFirst (Definite word1) (Unknown _ firsts) = elem (head word1) firsts
validateFirstToFirst (Unknown _ firsts) (Definite word2) = elem (head word2) firsts
validateFirstToFirst (Unknown _ firsts1) (Unknown _ firsts2) = not . null . intersect firsts1 $ firsts2

groupN :: Int -> [a] -> [[a]]
groupN _ [] = []
groupN n l
  | n > 0 = (take n l) : (groupN n (drop n l))
  | otherwise = error "Negative n"

main = do
   return ()

