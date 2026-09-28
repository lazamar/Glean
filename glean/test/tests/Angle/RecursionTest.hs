{-
  Copyright (c) Meta Platforms, Inc. and affiliates.
  All rights reserved.

  This source code is licensed under the BSD-style license found in the
  LICENSE file in the root directory of this source tree.
-}

{-# LANGUAGE QuasiQuotes #-}
module Angle.RecursionTest (main) where

import Control.Exception
import Control.Monad (forM_)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BC
import Data.Default (def)
import Data.Int (Int64)
import Data.List (isInfixOf, sort)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text, unpack)
import Test.HUnit

import TestRunner
import Util.String.Quasi

import Glean.Angle.Types (AngleVersion(..), Type_(NatTy), latestAngleVersion)
import Glean.Database.Schema.Types
import Glean.Database.Config (Config(..))
import Glean.Database.Types (Env)
import Glean.Init
import Glean (userQuery)
import qualified Glean.RTS.Term as RTS
import qualified Glean.RTS.Types as RTS
import Glean.Schema.Util
import Glean.Types as Thrift

import Schema.Lib

enableRecursion :: Config -> Config
enableRecursion settings = settings { cfgEnableRecursion = True }

recursionTest :: Test
recursionTest = TestList
  [ TestLabel "compiles" $ TestCase $ do
    -- doesn't get stuck expanding recursive terms.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              (Edge { A, B }) | (Path { A, K }; Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          ]
      ]
      $ \env repo schema -> do
        response <- runQ env repo [s| x.Path _ |]
        facts <- decodeResultsAs "x.Path.1" schema response
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 2, RTS.Nat 3 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 3 ]
          ]
          facts

  , TestLabel "calculates recursive relation with fixed arguments" $
    TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              (Edge { A, B }) | (Path { A, K }; Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3 -> 4 -> 5
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 4 } }|]
          , [s|{ "key": { "from": 4, "to": 5 } }|]
          ]
      ]
      $ \env repo schema -> do
        response <- runQ env repo [s| x.Path { 1, _ } |]
        facts <- decodeResultsAs "x.Path.1" schema response
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 3 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 4 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 5 ]
          ]
          facts

  , TestLabel "non-linear recursion typechecks" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              (Path { A, X }; Path { X, B }) | Edge { A, B }
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          ]
      ]
      $ \_ _ _ -> return ()

  , TestLabel "mutual recursion typechecks" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          predicate P : nat
          predicate Q : nat
          predicate R : nat
            A where P A | S A
          predicate S : nat
            A where Q A | R A
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.P" 1)
          [ [s|{ "key": 1 }|]
          ]
      ]
      $ \_ _ _ -> return ()

  , TestLabel "cycle closed by a later derive declaration" $ TestCase $ do
    -- P is declared without a derivation in x.1 and only gets one in x.2,
    -- closing the cycle P -> Q -> P across schemas.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          predicate Base : nat
          predicate P : nat
          predicate Q : nat
            A where x.P.1 A
        }
        schema x.2 : x.1 {
          derive x.P.1
            A where x.Base.1 A | x.Q.1 A
        }
        schema all.1 : x.2 {}
      |]
      [ mkBatch (PredicateRef "x.Base" 1)
          [ [s|{ "key": 1 }|]
          , [s|{ "key": 2 }|]
          ]
      ]
      $ \env repo schema -> do
        p <- decodeResultsAs "x.P.1" schema =<< runQ env repo [s| x.P.1 _ |]
        assertEqual "P uses the derivation from x.2"
          [ RTS.Nat 1, RTS.Nat 2 ] p
        q <- decodeResultsAs "x.Q.1" schema =<< runQ env repo [s| x.Q.1 _ |]
        assertEqual "Q sees P's derivation from x.2"
          [ RTS.Nat 1, RTS.Nat 2 ] q

  , TestLabel "recursion using a non-recursive derived predicate" $
    TestCase $ do
    -- Step is derived but not recursive, so it is inlined into each
    -- expansion of Path.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Step : { from: Node, to: Node }
            { A, B } where Edge { A, B }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              Step { A, B } | (Path { A, K }; Step { K, B })
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.Path.1" schema =<< runQ env repo
          [s| x.Path _ |]
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 3 ]
          , RTS.Tuple [ RTS.Nat 2, RTS.Nat 3 ]
          ]
          (sort facts)

  , TestLabel "derived predicate whose type refers to itself" $
    TestCase $ do
    -- Chain copies a linked list of Node facts, so the key of each
    -- derived Chain fact refers to another derived Chain fact.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          predicate Node : { label : nat, next : maybe Node }
          predicate Chain : { label : nat, next : maybe Chain }
            { L, N } where
              Node { L, M };
              (M = nothing; N = nothing) |
              (M = { just = Node { L2, _ } }; N = { just = Chain { L2, _ } })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3
      [ mkBatch (PredicateRef "x.Node" 1)
          [ [s|{ "id": 1, "key": { "label": 3 } }|]
          , [s|{ "id": 2, "key": { "label": 2, "next": 1 } }|]
          , [s|{ "id": 3, "key": { "label": 1, "next": 2 } }|]
          ]
      ]
      $ \env repo schema -> do
        chains <- decodeResultsAs "x.Chain.1" schema =<< runQ env repo
          [s| x.Chain _ |]
        assertEqual "one Chain fact per Node" 3 (length chains)
        list <- decodeResultsAs "x.Chain.1" schema =<< runQ env repo
          [s| x.Chain { 1, { just = x.Chain { 2, { just = x.Chain { 3, nothing } } } } } |]
        assertEqual "Chain facts form the same list as Node facts"
          1 (length list)

  , TestLabel "accepts negation of a non-recursive predicate in recursion" $
    TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Blocked : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              (x.Edge { A, B }; !(x.Blocked { A, B })) |
              (x.Path { A, K }; x.Edge { K, B }; !(x.Blocked { K, B }))
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -x-> 3 -> 4
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 4 } }|]
          ]
      , mkBatch (PredicateRef "x.Blocked" 1)
          [ [s|{ "key": { "from": 2, "to": 3 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.Path.1" schema =<< runQ env repo
          [s| x.Path _ |]
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 3, RTS.Nat 4 ]
          ]
          (sort facts)

  , TestLabel "left recursion with the last field bound" $ TestCase $ do
    -- Deriving Path { _, 4 } needs Path facts that don't end in 4.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3 -> 4
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 4 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.Path.1" schema =<< runQ env repo
          [s| x.Path { _, 4 } |]
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 4 ]
          , RTS.Tuple [ RTS.Nat 2, RTS.Nat 4 ]
          , RTS.Tuple [ RTS.Nat 3, RTS.Nat 4 ]
          ]
          (sort facts)

  , TestLabel "two calls to a recursive predicate" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3 -> 4
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 4 } }|]
          ]
      ]
      $ \env repo _ -> do
        nodes <- decodeNats =<< runQ env repo
          [s| X where x.Path { 1, X }; x.Path { X, 4 } |]
        assertEqual "nodes between 1 and 4" [ RTS.Nat 2, RTS.Nat 3 ]
          (sort nodes)

  , TestLabel "mutual recursion" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          predicate P : nat
          predicate Q : nat
          predicate R : nat
            A where x.P A | x.S A
          predicate S : nat
            A where x.Q A | x.R A
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.P" 1) [ [s|{ "key": 1 }|] ]
      , mkBatch (PredicateRef "x.Q" 1) [ [s|{ "key": 2 }|] ]
      ]
      $ \env repo schema -> do
        r <- decodeResultsAs "x.R.1" schema =<< runQ env repo [s| x.R _ |]
        assertEqual "R" [ RTS.Nat 1, RTS.Nat 2 ] (sort r)
        s <- decodeResultsAs "x.S.1" schema =<< runQ env repo [s| x.S _ |]
        assertEqual "S" [ RTS.Nat 1, RTS.Nat 2 ] (sort s)

  , TestLabel "cyclic data" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 <-> 2
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 1 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.Path.1" schema =<< runQ env repo
          [s| x.Path _ |]
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 1 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 2, RTS.Nat 1 ]
          , RTS.Tuple [ RTS.Nat 2, RTS.Nat 2 ]
          ]
          (sort facts)

  , TestLabel "negation of a recursive predicate" $ TestCase $ do
    -- The design doc's example: routes that need a flight because there
    -- is no land route.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Town = nat
          predicate Road : { begin : Town, end : Town }
          predicate FlightRoute : { from : Town, to : Town }
          predicate LandRoute : { from : Town, to : Town }
            { From, To } where
              x.Road { From, To } |
              (x.LandRoute { From, X }; x.Road { X, To })
          predicate NeedsFlying : { from : Town, to : Town }
            { From, To } where
              !(x.LandRoute { From, To });
              x.FlightRoute { From, To } |
              (x.NeedsFlying { From, X }; x.FlightRoute { X, To })
        }
        schema all.1 : x.1 {}
      |]
      -- roads 1 -> 2 -> 3, flights 1 -> 3 -> 4
      [ mkBatch (PredicateRef "x.Road" 1)
          [ [s|{ "key": { "begin": 1, "end": 2 } }|]
          , [s|{ "key": { "begin": 2, "end": 3 } }|]
          ]
      , mkBatch (PredicateRef "x.FlightRoute" 1)
          [ [s|{ "key": { "from": 1, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 4 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.NeedsFlying.1" schema =<< runQ env repo
          [s| x.NeedsFlying _ |]
        -- 1 -> 3 can be done by land, and every route from 1 to 4
        -- goes through 1 -> 3
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 3, RTS.Nat 4 ] ]
          (sort facts)

  , TestLabel "negated call followed by the same call" $ TestCase $ do
    -- The negation stops as soon as it finds a path. If that could leave
    -- the derivation for its demand unfinished, the second call, which
    -- has the same demand, would find the demand already there, take it
    -- as satisfied, and miss results. See Note [Semi-naive evaluation].
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> ... -> 10
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ "{ \"key\": { \"from\": " <> BC.pack (show n) <>
            ", \"to\": " <> BC.pack (show (n + 1)) <> " } }"
          | n <- [1 .. 9 :: Int]
          ]
      ]
      $ \env repo _ -> do
        nodes <- decodeNats =<< runQ env repo
          [s| X where (!(x.Path { 1, _ }); X = 0) | x.Path { 1, X } |]
        assertEqual "nodes reachable from 1"
          (map RTS.Nat [2 .. 10]) (sort nodes)

  , TestLabel "recursion must be enabled" $ TestCase $ do
    withSchemaAndFacts []
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          ]
      ]
      $ \env repo _ -> do
        r <- runQ env repo [s| x.Path _ |]
        case r of
          Left (BadQuery err) ->
            assertBool (unpack err) $
              "recursive reference to predicate" `isInfixOf` unpack err
          Right _ -> assertFailure "query succeeded"

  , TestLabel "no continuations" $ TestCase $ do
    -- A continuation would resume without the facts derived for Path.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          ]
      ]
      $ \env repo _ -> do
        r <- try $ userQuery env repo $ def
          { userQuery_query = [s| x.Path _ |]
          , userQuery_options = Just def
            { userQueryOptions_syntax = QuerySyntax_ANGLE
            , userQueryOptions_max_results = Just 1
            }
          }
        case r of
          Left (BadQuery err) ->
            assertBool (unpack err) $
              "reached one of its limits" `isInfixOf` unpack err
          Right _ -> assertFailure "query succeeded"

  , TestLabel "input from the call site" $ TestCase $ do
    -- The design doc's bounded recursion: Max only comes from the call
    -- site, so the facts can only be derived for the demanded Max.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate BoundedPath :
            { from: Node, to: Node, distance: nat, max: nat }
            { From, To, Distance, Max } where
              (x.Edge { From, To }; Distance = 1) |
              ( x.BoundedPath { From, K, D, Max };
                D < Max;
                x.Edge { K, To };
                Distance = D + 1 )
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3 -> 1
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 1 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.BoundedPath.1" schema =<< runQ env repo
          [s| x.BoundedPath { 1, _, _, 2 } |]
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 2, RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 3, RTS.Nat 2, RTS.Nat 2 ]
          ]
          (sort facts)

  , TestLabel "keeps values of any type across a recursive call" $
    TestCase $ do
    -- A and K are strings bound before the recursive call and used after
    -- it, and the key has a nested record.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          predicate Edge : { from: string, to: string }
          predicate Hops :
            { from: string, to: string, first: { name: string, hops: nat } }
            { A, B, { K, H } } where
              x.Edge { A, K };
              ( B = K; H = 1 ) |
              ( x.Hops { K, B, { _, N } }; H = N + 1 )
        }
        schema all.1 : x.1 {}
      |]
      -- a -> b -> c -> d
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": "a", "to": "b" } }|]
          , [s|{ "key": { "from": "b", "to": "c" } }|]
          , [s|{ "key": { "from": "c", "to": "d" } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.Hops.1" schema =<< runQ env repo
          [s| x.Hops { "a", _, _ } |]
        assertEqual "result content"
          [ RTS.Tuple
              [ RTS.String "a", RTS.String to
              , RTS.Tuple [ RTS.String "b", RTS.Nat hops ] ]
          | (to, hops) <- [ ("b", 1), ("c", 2), ("d", 3) ] ]
          (sort facts)

  , TestLabel "only derives what the call needs" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3, and 10 -> 11 -> ... -> 40, which isn't reachable
      -- from 1
      [ mkBatch (PredicateRef "x.Edge" 1) $
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          ] <>
          [ "{ \"key\": { \"from\": " <> BC.pack (show n) <>
            ", \"to\": " <> BC.pack (show (n + 1)) <> " } }"
          | n <- [10 .. 39 :: Int]
          ]
      ]
      $ \env repo schema -> do
        response <- runQ env repo [s| x.Path { 1, _ } |]
        facts <- decodeResultsAs "x.Path.1" schema response
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat 1, RTS.Nat 2 ]
          , RTS.Tuple [ RTS.Nat 1, RTS.Nat 3 ]
          ]
          (sort facts)
        edge <- either (assertFailure . unpack) (return . predicatePid) $
          lookupPredicateSourceRef (parseRef "x.Edge.1") LatestSchema schema
        let
          searched = case response of
            Right UserQueryResults{..} -> fromMaybe 0 $ do
              stats <- userQueryResults_stats
              counts <- userQueryStats_facts_searched stats
              Map.lookup (fromIntegral (RTS.fromPid edge)) counts
            Left _ -> 0
        assertBool ("Edge facts searched: " <> show searched) $
          searched > 0 && searched < 30

  , TestLabel "non-linear recursion" $ TestCase $ do
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              (x.Path { A, X }; x.Path { X, B }) | x.Edge { A, B }
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> 3 -> 4
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ [s|{ "key": { "from": 1, "to": 2 } }|]
          , [s|{ "key": { "from": 2, "to": 3 } }|]
          , [s|{ "key": { "from": 3, "to": 4 } }|]
          ]
      ]
      $ \env repo schema -> do
        facts <- decodeResultsAs "x.Path.1" schema =<< runQ env repo
          [s| x.Path _ |]
        assertEqual "result content"
          [ RTS.Tuple [ RTS.Nat a, RTS.Nat b ]
          | a <- [1..4], b <- [a+1..4] ]
          (sort facts)

  , TestLabel "repeated calls reuse derived facts" $ TestCase $ do
    -- The second call runs once for each result of the first, always
    -- with the same demand, which the first call already satisfied. It
    -- shouldn't search any more edges.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> ... -> 20
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ "{ \"key\": { \"from\": " <> BC.pack (show n) <>
            ", \"to\": " <> BC.pack (show (n + 1)) <> " } }"
          | n <- [1 .. 19 :: Int]
          ]
      ]
      $ \env repo schema -> do
        edge <- either (assertFailure . unpack) (return . predicatePid) $
          lookupPredicateSourceRef (parseRef "x.Edge.1") LatestSchema schema
        let
          searched :: Either BadQuery UserQueryResults -> Int64
          searched response = case response of
            Right UserQueryResults{..} -> fromMaybe 0 $ do
              stats <- userQueryResults_stats
              counts <- userQueryStats_facts_searched stats
              Map.lookup (fromIntegral (RTS.fromPid edge)) counts
            Left err -> error (show err)
        once <- runQ env repo [s| x.Path { 1, _ } |]
        repeated <- runQ env repo
          [s| { X, Y } where x.Path { 1, X }; x.Path { 1, Y } |]
        assertEqual "Edge facts searched" (searched once) (searched repeated)

  , TestLabel "resumes a derivation once for each fact" $ TestCase $ do
    -- All the facts of x.Path { 1, _ } are derived for the same demand.
    -- Each x.Path { 1, K } should search for the edges from K once, not
    -- once in every round after it was derived.
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
        }
        schema all.1 : x.1 {}
      |]
      -- 1 -> 2 -> ... -> 100
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ "{ \"key\": { \"from\": " <> BC.pack (show n) <>
            ", \"to\": " <> BC.pack (show (n + 1)) <> " } }"
          | n <- [1 .. 99 :: Int]
          ]
      ]
      $ \env repo schema -> do
        response <- runQ env repo [s| x.Path { 1, _ } |]
        facts <- decodeResultsAs "x.Path.1" schema response
        assertEqual "results" 99 (length facts)
        searched <- factsSearched schema "x.Edge.1" response
        assertBool ("Edge facts searched: " <> show searched) $
          searched < 200
  ]

-- | How many facts of a predicate a query searched
factsSearched
  :: DbSchema
  -> Text
  -> Either BadQuery UserQueryResults
  -> IO Int64
factsSearched schema ref response = do
  pid <- either (assertFailure . unpack) (return . predicatePid) $
    lookupPredicateSourceRef (parseRef ref) LatestSchema schema
  case response of
    Right UserQueryResults{..} -> return $ fromMaybe 0 $ do
      stats <- userQueryResults_stats
      counts <- userQueryStats_facts_searched stats
      Map.lookup (fromIntegral (RTS.fromPid pid)) counts
    Left err -> assertFailure (show err)

decodeNats :: Either BadQuery UserQueryResults -> IO [RTS.Value]
decodeNats response =
  decodeResults NatTy userQueryResultsBin_facts response
    >>= either assertFailure return

runQ :: Env -> Repo -> ByteString -> IO (Either BadQuery UserQueryResults)
runQ env repo query =
  try $ userQuery env repo $ def
    { userQuery_query = query
    , userQuery_options = Just def
      { userQueryOptions_syntax = QuerySyntax_ANGLE
      , userQueryOptions_recursive = True
      , userQueryOptions_collect_facts_searched = True
      , userQueryOptions_debug = def
        { queryDebugOptions_bytecode = False
        , queryDebugOptions_ir = False
        }
      }
    , userQuery_encodings = [ UserQueryEncoding_bin def ]
    }

decodeResultsAs
  :: Text
  -> DbSchema
  -> Either BadQuery UserQueryResults
  -> IO [RTS.Value]
decodeResultsAs ref schema eresults = do
  res <- decodeResults
    (keyType (parseRef ref) schema) userQueryResultsBin_facts eresults
  either assertFailure return res
  where
  keyType
    :: SourceRef
    -> DbSchema
    -> RTS.Type
  keyType ref dbSchema =
    case lookupPredicateSourceRef ref LatestSchema dbSchema of
      Left err -> error $ "can't find predicate: " <>
        unpack (showRef ref) <> ": " <> unpack err
      Right details -> predicateKeyType details

stratificationTest :: Test
stratificationTest = TestList
  [ TestLabel "rejects recursion through negation" $ TestCase $
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          predicate Base : nat
          predicate P : nat
            A where x.Base A; !(x.Q A)
          predicate Q : nat
            A where x.P A
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected "x.P.1 -> !x.Q.1 -> x.P.1")

  , TestLabel "rejects a predicate negating itself" $ TestCase $
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          predicate Base : nat
          predicate P : nat
            A where x.Base A; !(x.P A)
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected "x.P.1 -> !x.P.1")

  , TestLabel "rejects recursion through an if condition" $ TestCase $
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          predicate Base : nat
          predicate P : nat
            B where x.Base A; B = if (x.P A) then A else 0
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected "x.P.1 -> !x.P.1")

  , TestLabel "rejects recursion through all" $ TestCase $
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          predicate Base : nat
          predicate P : nat
            A where x.Base A; _ = all (x.P A)
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected "x.P.1 -> !x.P.1")

  , TestLabel "accepts negation of a recursive predicate outside its cycle" $
    TestCase $
    -- NeedsFlying and LandRoute are both recursive, and NeedsFlying
    -- negates LandRoute, but LandRoute doesn't depend on NeedsFlying.
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          type Town = nat
          predicate Road : { begin : Town, end : Town }
          predicate FlightRoute : { from : Town, to : Town }
          predicate LandRoute : { from : Town, to : Town }
            { From, To } where
              x.Road { From, To } |
              (x.LandRoute { From, X }; x.Road { X, To })
          predicate NeedsFlying : { from : Town, to : Town }
            { From, To } where
              !(x.LandRoute { From, To });
              x.FlightRoute { From, To } |
              (x.NeedsFlying { From, X }; x.FlightRoute { X, To })
        }
        schema all.1 : x.1 {}
      |]
      (either (assertFailure . show) return)
  ]

storedTest :: Test
storedTest = TestList
  [ TestLabel "rejects a recursive stored predicate" $ TestCase $
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          predicate Base : nat
          predicate P : nat
            stored A where x.Base A | x.P A
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected "x.P.1 is recursive")

  , TestLabel "rejects a stored predicate in a cycle" $ TestCase $
    -- S is stored and R isn't, but deriving S expands R, which refers
    -- back to S.
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          predicate Base : nat
          predicate S : nat
            stored A where x.R A
          predicate R : nat
            A where x.Base A | x.S A
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected "x.S.1 is recursive")

  , TestLabel "rejects a stored predicate using recursion" $ TestCase $
    withSchema latestAngleVersion
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Path : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Path { A, K }; x.Edge { K, B })
          predicate Reachable : Node
            stored B where x.Path { 1, B }
        }
        schema all.1 : x.1 {}
      |]
      (assertRejected
        "x.Reachable.1 depends on the recursive predicate x.Path.1")

  , TestLabel "accepts a stored predicate using default derivations" $
    TestCase $
    -- P.1 and P.2 derive each other, but only one of the two derivations
    -- is ever enabled, so Stored doesn't depend on recursion.
    withSchema (AngleVersion 11)
      [s|
        schema test.1 {
          predicate P : { a : string, b : nat }
        }
        schema test.2 : test.1 {
          predicate P : { a : string, b : nat, c : {} }

          derive test.P.1 default
            { A, B } where P.2 { A, B, _ }

          derive test.P.2 default
            { A, B, {} } where test.P.1 { A, B }

          predicate Stored : string
            stored A where test.P.1 { A, _ }
        }
        schema all.1 : test.1, test.2 {}
      |]
      (either (assertFailure . show) return)
  ]

-- | Compare the results of recursive queries with a reference
-- implementation, on a few pseudo-random graphs.
referenceTest :: Test
referenceTest = TestList
  [ TestLabel ("graph " <> show n) $ TestCase $ checkGraph nodes edges
  | (n, (seed, nodes, size)) <- zip [1 :: Int ..] graphs
  , let edges = randomGraph seed nodes size
  ]
  where
  -- (seed, number of nodes, number of edges)
  graphs = [ (1, 6, 8), (2, 8, 14), (3, 10, 12), (4, 5, 12) ]

  -- the same relation defined in different ways
  predicates =
    [ "x.Left.1", "x.Right.1", "x.NonLinear.1", "x.Mutual.1"
    , "x.Nested.1", "x.Then.1", "x.Else.1", "x.Composed.1" ]

  checkGraph nodes edges =
    withSchemaAndFacts [enableRecursion]
      [s|
        schema x.1 {
          type Node = nat
          predicate Edge : { from: Node, to: Node }
          predicate Left : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Left { A, K }; x.Edge { K, B })
          predicate Right : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Edge { A, K }; x.Right { K, B })
          predicate NonLinear : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.NonLinear { A, K }; x.NonLinear { K, B })
          # mutual recursion
          predicate Mutual : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Edge { A, K }; x.MutualStep { K, B })
          predicate MutualStep : { from: Node, to: Node }
            { A, B } where x.Mutual { A, B }
          # calls in alternatives of a disjunction and of an if
          predicate Nested : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, K };
              B = (K | (X where x.Nested { K, X }))
          predicate Then : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, K };
              B = if (x.Edge { K, _ })
                then (K | (X where x.Then { K, X }))
                else K
          predicate Else : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, K };
              B = if (K = 0) then K else (K | (X where x.Else { K, X }))
          # a call to a lower component after a call to its own
          predicate Composed : { from: Node, to: Node }
            { A, B } where
              x.Edge { A, B } | (x.Composed { A, K }; x.Right { K, B })
        }
        schema all.1 : x.1 {}
      |]
      [ mkBatch (PredicateRef "x.Edge" 1)
          [ "{ \"key\": { \"from\": " <> BC.pack (show a) <>
            ", \"to\": " <> BC.pack (show b) <> " } }"
          | (a, b) <- edges
          ]
      ]
      $ \env repo schema -> do
        let
          expected = closure edges
          check predicate query want = do
            facts <- decodeResultsAs predicate schema =<<
              runQ env repo (BC.pack (unpack predicate <> " " <> query))
            assertEqual (unpack predicate <> " " <> query)
              (Set.toList want) (sort (map pair facts))
        forM_ predicates $ \predicate -> do
          check predicate "_" expected
          forM_ [1 .. nodes] $ \a ->
            check predicate ("{ " <> show a <> ", _ }") $
              Set.filter ((== a) . fst) expected
          forM_ [1 .. nodes] $ \b ->
            check predicate ("{ _, " <> show b <> " }") $
              Set.filter ((== b) . snd) expected

  pair (RTS.Tuple [RTS.Nat a, RTS.Nat b]) = (fromIntegral a, fromIntegral b)
  pair v = error ("unexpected result: " <> show v)

-- | Pseudo-random edges between nodes 1..n, from a linear congruential
-- generator so that the graphs are the same on every run. Its low bits
-- are far from random, so we use the high ones.
randomGraph :: Int -> Int -> Int -> [(Int, Int)]
randomGraph seed nodes size = Set.toList $ Set.fromList $ take size $
  pairs (map node (drop 1 (iterate next seed)))
  where
  next x = (x * 1103515245 + 12345) `mod` 2147483648
  node x = 1 + (x `div` 65536) `mod` nodes
  pairs (a : b : rest) = (a, b) : pairs rest
  pairs _ = []

-- | The transitive closure of a set of edges.
closure :: [(Int, Int)] -> Set (Int, Int)
closure edges = go (Set.fromList edges)
  where
  go paths
    | paths' == paths = paths
    | otherwise = go paths'
    where
    paths' = Set.union paths $ Set.fromList
      [ (a, c) | (a, b) <- Set.toList paths, (b', c) <- edges, b == b' ]

assertRejected :: String -> Either SomeException () -> IO ()
assertRejected expected r = case r of
  Left err ->
    assertBool ("error should mention " <> expected <> ":\n" <> show err) $
      expected `isInfixOf` show err
  Right () -> assertFailure "schema was accepted"

main :: IO ()
main = withUnitTest $ testRunner $ TestList
  [ TestLabel "recursion" recursionTest
  , TestLabel "stratification" stratificationTest
  , TestLabel "stored predicates" storedTest
  , TestLabel "reference" referenceTest
  ]
