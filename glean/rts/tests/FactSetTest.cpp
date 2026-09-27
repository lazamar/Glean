/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree.
 */

#include "glean/rts/factset.h"
#include <gtest/gtest.h>
#include <algorithm>
#include <string>
#include <vector>
#include "glean/rts/binary.h"

using namespace facebook::glean::rts;
using namespace facebook::glean;

namespace {

Fact::Clause clauseFrom(const unsigned char* d, size_t total, size_t ks) {
  return Fact::Clause::from(folly::ByteRange(d, total), ks);
}

std::vector<Id> collectIds(FactIterator& iter) {
  std::vector<Id> ids;
  for (auto ref = iter.get(); ref; iter.next(), ref = iter.get()) {
    ids.push_back(ref.id);
  }
  return ids;
}

std::vector<std::string> collectKeys(FactIterator& iter) {
  std::vector<std::string> keys;
  for (auto ref = iter.get(); ref; iter.next(), ref = iter.get()) {
    keys.push_back(ref.key().str());
  }
  return keys;
}

} // namespace

TEST(FactSetTest, DefineAddsFactAndAdvancesId) {
  FactSet fs(Id::lowest());
  unsigned char data[] = "keyval";
  auto id = fs.define(Pid::lowest(), clauseFrom(data, 6, 3));
  EXPECT_EQ(id, Id::lowest());
  EXPECT_EQ(fs.size(), 1);
  EXPECT_FALSE(fs.empty());
  EXPECT_EQ(fs.firstFreeId(), Id::lowest() + 1);
}

TEST(FactSetTest, DefineDuplicateReturnsSameId) {
  FactSet fs(Id::lowest());
  unsigned char data[] = "keyval";
  auto id1 = fs.define(Pid::lowest(), clauseFrom(data, 6, 3));
  auto id2 = fs.define(Pid::lowest(), clauseFrom(data, 6, 3));
  EXPECT_EQ(id1, id2);
  EXPECT_EQ(fs.size(), 1);
}

TEST(FactSetTest, DefineSameKeyDiffValueReturnsInvalid) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "keyAAA";
  unsigned char d2[] = "keyBBB";
  fs.define(Pid::lowest(), clauseFrom(d1, 6, 3));
  auto id2 = fs.define(Pid::lowest(), clauseFrom(d2, 6, 3));
  EXPECT_EQ(id2, Id::invalid());
}

TEST(FactSetTest, DefineDifferentKeysGetDistinctIds) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "aaa";
  unsigned char d2[] = "bbb";
  auto id1 = fs.define(Pid::lowest(), clauseFrom(d1, 3, 3));
  auto id2 = fs.define(Pid::lowest(), clauseFrom(d2, 3, 3));
  EXPECT_NE(id1, id2);
  EXPECT_EQ(fs.size(), 2);
}

TEST(FactSetTest, TypeByIdReturnsCorrectTypeOrInvalid) {
  FactSet fs(Id::lowest());
  auto pid1 = Pid::lowest();
  auto pid2 = Pid::lowest() + 1;
  unsigned char d1[] = "aa";
  unsigned char d2[] = "bb";
  auto id1 = fs.define(pid1, clauseFrom(d1, 2, 2));
  auto id2 = fs.define(pid2, clauseFrom(d2, 2, 2));
  EXPECT_EQ(fs.typeById(id1), pid1);
  EXPECT_EQ(fs.typeById(id2), pid2);
  EXPECT_EQ(fs.typeById(Id::lowest() + 99), Pid::invalid());
  EXPECT_EQ(fs.typeById(Id::invalid()), Pid::invalid());
}

TEST(FactSetTest, IdByKeyFindsExistingOrReturnsInvalid) {
  FactSet fs(Id::lowest());
  unsigned char data[] = "mykey";
  auto id = fs.define(Pid::lowest(), clauseFrom(data, 5, 5));
  EXPECT_EQ(fs.idByKey(Pid::lowest(), folly::ByteRange(data, 5)), id);
  unsigned char missing[] = "nope";
  EXPECT_EQ(
      fs.idByKey(Pid::lowest(), folly::ByteRange(missing, 4)), Id::invalid());
}

TEST(FactSetTest, FactByIdCallbackReceivesCorrectData) {
  FactSet fs(Id::lowest());
  unsigned char data[] = "keyval";
  auto id = fs.define(Pid::lowest(), clauseFrom(data, 6, 3));
  Pid gotType = Pid::invalid();
  size_t gotKeySize = 0;
  size_t gotValSize = 0;
  bool found = fs.factById(id, [&](Pid t, Fact::Clause c) {
    gotType = t;
    gotKeySize = c.key_size;
    gotValSize = c.value_size;
  });
  EXPECT_TRUE(found);
  EXPECT_EQ(gotType, Pid::lowest());
  EXPECT_EQ(gotKeySize, 3);
  EXPECT_EQ(gotValSize, 3);
}

TEST(FactSetTest, FactByIdReturnsFalseForMissing) {
  FactSet fs(Id::lowest());
  bool found = fs.factById(Id::lowest(), [](Pid, Fact::Clause) {});
  EXPECT_FALSE(found);
}

TEST(FactSetTest, CountReturnsNumberOfFactsPerPredicate) {
  FactSet fs(Id::lowest());
  auto pid1 = Pid::lowest();
  auto pid2 = Pid::lowest() + 1;
  unsigned char d1[] = "a";
  unsigned char d2[] = "b";
  unsigned char d3[] = "c";
  fs.define(pid1, clauseFrom(d1, 1, 1));
  fs.define(pid1, clauseFrom(d2, 1, 1));
  fs.define(pid2, clauseFrom(d3, 1, 1));
  EXPECT_EQ(fs.count(pid1).low(), 2);
  EXPECT_EQ(fs.count(pid2).low(), 1);
  EXPECT_EQ(fs.count(Pid::lowest() + 99).low(), 0);
}

TEST(FactSetTest, EnumerateIteratesAllFacts) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "aa";
  unsigned char d2[] = "bb";
  fs.define(Pid::lowest(), clauseFrom(d1, 2, 2));
  fs.define(Pid::lowest(), clauseFrom(d2, 2, 2));
  auto iter = fs.enumerate();
  std::vector<Id> ids;
  for (auto ref = iter->get(); ref; iter->next(), ref = iter->get()) {
    ids.push_back(ref.id);
  }
  std::vector<Id> expected{Id::lowest(), Id::lowest() + 1};
  EXPECT_EQ(ids, expected);
}

TEST(FactSetTest, EnumerateWithBounds) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "a";
  unsigned char d2[] = "b";
  unsigned char d3[] = "c";
  fs.define(Pid::lowest(), clauseFrom(d1, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d2, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d3, 1, 1));
  auto iter = fs.enumerate(Id::lowest() + 1, Id::lowest() + 2);
  auto ref = iter->get();
  ASSERT_TRUE(bool(ref));
  EXPECT_EQ(ref.id, Id::lowest() + 1);
  iter->next();
  EXPECT_FALSE(bool(iter->get()));
}

TEST(FactSetTest, EnumerateBackIteratesReverse) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "a";
  unsigned char d2[] = "b";
  unsigned char d3[] = "c";
  fs.define(Pid::lowest(), clauseFrom(d1, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d2, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d3, 1, 1));
  auto iter = fs.enumerateBack();
  std::vector<Id> ids;
  for (auto ref = iter->get(); ref; iter->next(), ref = iter->get()) {
    ids.push_back(ref.id);
  }
  std::vector<Id> expected{Id::lowest() + 2, Id::lowest() + 1, Id::lowest()};
  EXPECT_EQ(ids, expected);
}

TEST(FactSetTest, AppendCombinesTwoSets) {
  FactSet fs1(Id::lowest());
  unsigned char d1[] = "aa";
  fs1.define(Pid::lowest(), clauseFrom(d1, 2, 2));

  FactSet fs2(fs1.firstFreeId());
  unsigned char d2[] = "bb";
  fs2.define(Pid::lowest(), clauseFrom(d2, 2, 2));

  EXPECT_TRUE(fs1.appendable(fs2));
  fs1.append(std::move(fs2));
  EXPECT_EQ(fs1.size(), 2);
  EXPECT_EQ(fs1.typeById(Id::lowest()), Pid::lowest());
  EXPECT_EQ(fs1.typeById(Id::lowest() + 1), Pid::lowest());
}

TEST(FactSetTest, AppendableReturnsFalseOnIdGap) {
  FactSet fs1(Id::lowest());
  unsigned char d1[] = "aa";
  fs1.define(Pid::lowest(), clauseFrom(d1, 2, 2));

  FactSet fs2(Id::lowest() + 100);
  unsigned char d2[] = "bb";
  fs2.define(Pid::lowest(), clauseFrom(d2, 2, 2));

  EXPECT_FALSE(fs1.appendable(fs2));
}

TEST(FactSetTest, AppendableReturnsFalseOnDuplicateKey) {
  FactSet fs1(Id::lowest());
  unsigned char d1[] = "same";
  fs1.define(Pid::lowest(), clauseFrom(d1, 4, 4));

  FactSet fs2(fs1.firstFreeId());
  unsigned char d2[] = "same";
  fs2.define(Pid::lowest(), clauseFrom(d2, 4, 4));

  EXPECT_FALSE(fs1.appendable(fs2));
}

TEST(FactSetTest, AppendableWithEmptySets) {
  FactSet fs1(Id::lowest());
  FactSet fs2(Id::lowest() + 999);
  EXPECT_TRUE(fs1.appendable(fs2));
  EXPECT_TRUE(fs2.appendable(fs1));
}

TEST(FactSetTest, SerializePreservesFactData) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "key1val1";
  unsigned char d2[] = "key2val2";
  fs.define(Pid::lowest(), clauseFrom(d1, 8, 4));
  fs.define(Pid::lowest(), clauseFrom(d2, 8, 4));
  auto serialized = fs.serialize();
  EXPECT_EQ(serialized.first, Id::lowest());
  EXPECT_EQ(serialized.count, 2);
  // Verify serialized data can be deserialized back to matching facts
  binary::Input input(serialized.facts.bytes());
  for (size_t i = 0; i < serialized.count; ++i) {
    Pid type = Pid::invalid();
    Fact::Clause clause;
    Fact::deserialize(input, type, clause);
    EXPECT_EQ(type, Pid::lowest());
    EXPECT_EQ(clause.key_size, 4);
    EXPECT_EQ(clause.value_size, 4);
  }
}

TEST(FactSetTest, AllocatedMemoryReflectsFactData) {
  FactSet fs(Id::lowest());
  auto memEmpty = fs.allocatedMemory();
  unsigned char data[] = "some_key_datasome_value_data";
  fs.define(Pid::lowest(), clauseFrom(data, 27, 14));
  auto memOne = fs.allocatedMemory();
  EXPECT_GT(memOne, memEmpty);
  // Memory should grow by at least the size of the fact data
  EXPECT_GE(memOne - memEmpty, 27);
}

TEST(FactSetTest, PredicateStatsTracksFactCounts) {
  FactSet fs(Id::lowest());
  auto pid1 = Pid::lowest();
  auto pid2 = Pid::lowest() + 1;
  unsigned char d1[] = "a";
  unsigned char d2[] = "b";
  unsigned char d3[] = "cc";
  fs.define(pid1, clauseFrom(d1, 1, 1));
  fs.define(pid1, clauseFrom(d2, 1, 1));
  fs.define(pid2, clauseFrom(d3, 2, 2));
  auto stats = fs.predicateStats();
  auto* s1 = stats.lookup(pid1);
  auto* s2 = stats.lookup(pid2);
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);
  EXPECT_EQ(s1->count, 2);
  EXPECT_EQ(s2->count, 1);
}

TEST(FactSetTest, PredicateStatsUpdatesAfterInitialRead) {
  FactSet fs(Id::lowest());
  const auto pid1 = Pid::lowest();
  const auto pid2 = Pid::lowest() + 1;
  unsigned char d1[] = "a";
  unsigned char d2[] = "bb";
  unsigned char d3[] = "ccc";

  fs.define(pid1, clauseFrom(d1, 1, 1));
  ASSERT_NE(fs.predicateStats().lookup(pid1), nullptr);

  fs.define(pid1, clauseFrom(d2, 2, 2));
  fs.define(pid2, clauseFrom(d3, 3, 3));

  const auto stats = fs.predicateStats();
  ASSERT_NE(stats.lookup(pid1), nullptr);
  ASSERT_NE(stats.lookup(pid2), nullptr);
  EXPECT_EQ(*stats.lookup(pid1), MemoryStats(2, 3));
  EXPECT_EQ(*stats.lookup(pid2), MemoryStats(1, 3));
}

TEST(FactSetTest, SeekWithNonexistentTypeReturnsEmpty) {
  FactSet fs(Id::lowest());
  unsigned char d[] = "key";
  fs.define(Pid::lowest(), clauseFrom(d, 3, 3));
  unsigned char prefix[] = "x";
  auto iter = fs.seek(
      Pid::lowest() + 99,
      folly::ByteRange(prefix, static_cast<size_t>(0)),
      std::nullopt);
  EXPECT_FALSE(bool(iter->get()));
}

TEST(FactSetTest, SeekReturnsOnlyMatchingPrefixInKeyOrder) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "band";
  unsigned char d2[] = "apple";
  unsigned char d3[] = "banana";
  unsigned char d4[] = "bar";
  unsigned char d5[] = "ban";

  fs.define(Pid::lowest(), clauseFrom(d1, 4, 4));
  fs.define(Pid::lowest(), clauseFrom(d2, 5, 5));
  fs.define(Pid::lowest(), clauseFrom(d3, 6, 6));
  fs.define(Pid::lowest(), clauseFrom(d4, 3, 3));
  fs.define(Pid::lowest(), clauseFrom(d5, 3, 3));

  unsigned char prefix[] = "ban";
  auto iter = fs.seek(Pid::lowest(), folly::ByteRange(prefix, 3), std::nullopt);
  const std::vector<std::string> expected{"ban", "banana", "band"};
  EXPECT_EQ(collectKeys(*iter), expected);
}

TEST(FactSetTest, SeekRestartResumesAtRestartFact) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "ban";
  unsigned char d2[] = "banana";
  unsigned char d3[] = "band";
  fs.define(Pid::lowest(), clauseFrom(d1, 3, 3));
  const auto restartId = fs.define(Pid::lowest(), clauseFrom(d2, 6, 6));
  fs.define(Pid::lowest(), clauseFrom(d3, 4, 4));

  auto restart = fs.enumerate(restartId, restartId + 1)->get();
  unsigned char prefix[] = "ban";
  auto iter = fs.seek(Pid::lowest(), folly::ByteRange(prefix, 3), restart);

  const std::vector<std::string> expected{"banana", "band"};
  EXPECT_EQ(collectKeys(*iter), expected);
}

TEST(FactSetTest, SeekIndexReflectsFactsAddedAfterFirstSeek) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "alpha";
  unsigned char d2[] = "alpine";
  unsigned char d3[] = "beta";
  fs.define(Pid::lowest(), clauseFrom(d1, 5, 5));

  unsigned char prefix[] = "al";
  auto firstSeek =
      fs.seek(Pid::lowest(), folly::ByteRange(prefix, 2), std::nullopt);
  const std::vector<std::string> initiallyExpected{"alpha"};
  EXPECT_EQ(collectKeys(*firstSeek), initiallyExpected);

  fs.define(Pid::lowest(), clauseFrom(d2, 6, 6));
  fs.define(Pid::lowest(), clauseFrom(d3, 4, 4));

  auto refreshedSeek =
      fs.seek(Pid::lowest(), folly::ByteRange(prefix, 2), std::nullopt);
  const std::vector<std::string> refreshedExpected{"alpha", "alpine"};
  EXPECT_EQ(collectKeys(*refreshedSeek), refreshedExpected);
}

// Recursive queries define facts of a predicate while a seek on the same
// predicate is in progress, and then seek again.
TEST(FactSetTest, SeekIteratorSurvivesFactsAddedDuringIteration) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "a1";
  unsigned char d2[] = "a2";
  unsigned char d3[] = "a3";
  fs.define(Pid::lowest(), clauseFrom(d1, 2, 2));
  fs.define(Pid::lowest(), clauseFrom(d3, 2, 2));

  unsigned char prefix[] = "a";
  auto outer =
      fs.seek(Pid::lowest(), folly::ByteRange(prefix, 1), std::nullopt);
  auto first = outer->get();
  ASSERT_TRUE(first);
  EXPECT_EQ(first.key().str(), "a1");

  // Define a fact and seek again, which updates the index.
  fs.define(Pid::lowest(), clauseFrom(d2, 2, 2));
  auto inner =
      fs.seek(Pid::lowest(), folly::ByteRange(prefix, 1), std::nullopt);
  const std::vector<std::string> all{"a1", "a2", "a3"};
  EXPECT_EQ(collectKeys(*inner), all);

  // The first seek carries on from where it was, and sees the new fact
  // because it comes later in key order.
  outer->next();
  const std::vector<std::string> rest{"a2", "a3"};
  EXPECT_EQ(collectKeys(*outer), rest);
}

// A seek indexes the facts added since the previous seek. Recursive queries
// alternate between adding facts and seeking, with facts of different
// predicates interleaved, and new keys can come before or after the keys
// already indexed.
TEST(FactSetTest, SeekIndexesFactsAddedBetweenSeeks) {
  FactSet fs(Id::lowest());
  const auto pid1 = Pid::lowest();
  const auto pid2 = Pid::lowest() + 1;
  auto define = [&](Pid pid, const std::string& key) {
    fs.define(
        pid,
        Fact::Clause::from(
            folly::ByteRange(
                reinterpret_cast<const unsigned char*>(key.data()), key.size()),
            key.size()));
  };
  std::vector<std::string> expected1, expected2;
  for (int round = 0; round < 5; ++round) {
    for (int i = 0; i < 4; ++i) {
      const auto key = std::to_string(i) + "-" + std::to_string(round);
      define(pid1, "a" + key);
      define(pid2, "b" + key);
      expected1.push_back("a" + key);
      expected2.push_back("b" + key);
    }
    std::sort(expected1.begin(), expected1.end());
    std::sort(expected2.begin(), expected2.end());
    EXPECT_EQ(
        collectKeys(*fs.seek(pid1, folly::ByteRange(), std::nullopt)),
        expected1);
    EXPECT_EQ(
        collectKeys(*fs.seek(pid2, folly::ByteRange(), std::nullopt)),
        expected2);
  }
}

TEST(FactSetTest, FactsByDifferentPredicatesAreIndependent) {
  FactSet fs(Id::lowest());
  auto pid1 = Pid::lowest();
  auto pid2 = Pid::lowest() + 1;
  unsigned char d[] = "samekey";
  auto id1 = fs.define(pid1, clauseFrom(d, 7, 7));
  auto id2 = fs.define(pid2, clauseFrom(d, 7, 7));
  EXPECT_NE(id1, id2);
  EXPECT_EQ(fs.idByKey(pid1, folly::ByteRange(d, 7)), id1);
  EXPECT_EQ(fs.idByKey(pid2, folly::ByteRange(d, 7)), id2);
}

TEST(FactSetTest, LookupBelowStartingIdReturnsNotFound) {
  FactSet fs(Id::lowest() + 10);
  unsigned char d[] = "x";
  fs.define(Pid::lowest(), clauseFrom(d, 1, 1));
  EXPECT_EQ(fs.typeById(Id::lowest()), Pid::invalid());
  EXPECT_EQ(fs.typeById(Id::lowest() + 9), Pid::invalid());
  EXPECT_EQ(fs.typeById(Id::lowest() + 10), Pid::lowest());
  bool found = fs.factById(Id::lowest(), [](Pid, Fact::Clause) {});
  EXPECT_FALSE(found);
}

TEST(FactSetTest, EnumerateBackWithBoundsMatchesForwardRangeInReverse) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "a";
  unsigned char d2[] = "b";
  unsigned char d3[] = "c";
  unsigned char d4[] = "d";
  fs.define(Pid::lowest(), clauseFrom(d1, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d2, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d3, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d4, 1, 1));

  auto iter = fs.enumerateBack(Id::lowest() + 3, Id::lowest() + 1);
  const std::vector<Id> expected{Id::lowest() + 2, Id::lowest() + 1};
  EXPECT_EQ(collectIds(*iter), expected);
}

TEST(FactSetTest, SeekWithinSectionFullRangeWorks) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "abc";
  unsigned char d2[] = "abd";
  fs.define(Pid::lowest(), clauseFrom(d1, 3, 3));
  fs.define(Pid::lowest(), clauseFrom(d2, 3, 3));
  unsigned char prefix[] = "ab";
  auto iter = fs.seekWithinSection(
      Pid::lowest(),
      folly::ByteRange(prefix, 2),
      Id::invalid(),
      Id::lowest() + 100,
      std::nullopt);
  size_t count = 0;
  for (auto ref = iter->get(); ref; iter->next(), ref = iter->get()) {
    ++count;
  }
  EXPECT_EQ(count, 2);
}

TEST(FactSetTest, SeekWithinSectionNarrowBoundsWithPrefix) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "abc";
  unsigned char d2[] = "abd";
  unsigned char d3[] = "abe";
  unsigned char d4[] = "xyz";
  fs.define(Pid::lowest(), clauseFrom(d1, 3, 3));
  auto id2 = fs.define(Pid::lowest(), clauseFrom(d2, 3, 3));
  fs.define(Pid::lowest(), clauseFrom(d3, 3, 3));
  fs.define(Pid::lowest(), clauseFrom(d4, 3, 3));

  unsigned char prefix[] = "ab";
  auto iter = fs.seekWithinSection(
      Pid::lowest(), folly::ByteRange(prefix, 2), id2, id2 + 2, std::nullopt);
  const std::vector<std::string> expected{"abd", "abe"};
  EXPECT_EQ(collectKeys(*iter), expected);
}

TEST(FactSetTest, SeekWithinSectionNarrowBoundsWithoutPrefix) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "a";
  unsigned char d2[] = "b";
  unsigned char d3[] = "c";
  unsigned char d4[] = "d";
  unsigned char d5[] = "e";
  auto other = Pid::lowest() + 1;
  fs.define(Pid::lowest(), clauseFrom(d1, 1, 1));
  auto id2 = fs.define(Pid::lowest(), clauseFrom(d2, 1, 1));
  fs.define(other, clauseFrom(d3, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d4, 1, 1));
  fs.define(Pid::lowest(), clauseFrom(d5, 1, 1));

  // fewer facts in the range than facts of the predicate
  auto narrow = fs.seekWithinSection(
      Pid::lowest(), folly::ByteRange(), id2, id2 + 3, std::nullopt);
  const std::vector<std::string> narrowExpected{"b", "d"};
  EXPECT_EQ(collectKeys(*narrow), narrowExpected);

  // more facts in the range than facts of the predicate
  auto wide = fs.seekWithinSection(
      other, folly::ByteRange(), Id::lowest(), id2 + 3, std::nullopt);
  const std::vector<std::string> wideExpected{"c"};
  EXPECT_EQ(collectKeys(*wide), wideExpected);

  // nothing in the range
  auto empty = fs.seekWithinSection(
      other, folly::ByteRange(), id2 + 2, id2 + 4, std::nullopt);
  EXPECT_EQ(collectKeys(*empty), std::vector<std::string>{});
}

TEST(FactSetTest, SeekWithinSectionSurvivesFactsAddedDuringIteration) {
  FactSet fs(Id::lowest());
  std::vector<std::string> keys;
  for (int i = 0; i < 10; ++i) {
    keys.push_back("k" + std::to_string(i));
  }
  auto define = [&](const std::string& key) {
    return fs.define(
        Pid::lowest(),
        Fact::Clause::from(
            folly::ByteRange(
                reinterpret_cast<const unsigned char*>(key.data()), key.size()),
            key.size()));
  };
  auto first = define(keys[0]);
  define(keys[1]);
  define(keys[2]);

  // Search the first two facts, and add many facts of the same predicate
  // while doing so.
  auto iter = fs.seekWithinSection(
      Pid::lowest(), folly::ByteRange(), first, first + 2, std::nullopt);
  std::vector<std::string> found;
  for (auto ref = iter->get(); ref; iter->next(), ref = iter->get()) {
    found.push_back(ref.key().str());
    for (int i = 3; i < 10; ++i) {
      define(keys[i] + "-" + std::to_string(found.size()));
    }
    // updates the index
    fs.seekWithinSection(
        Pid::lowest(), folly::ByteRange(), first, first + 1, std::nullopt);
  }
  const std::vector<std::string> expected{"k0", "k1"};
  EXPECT_EQ(found, expected);
}

TEST(FactSetTest, SeekWithinSectionCantRestartNarrowBounds) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "abc";
  unsigned char d2[] = "abd";
  auto id1 = fs.define(Pid::lowest(), clauseFrom(d1, 3, 3));
  fs.define(Pid::lowest(), clauseFrom(d2, 3, 3));

  unsigned char prefix[] = "ab";
  auto restart = fs.enumerate(id1, id1 + 1)->get();
  EXPECT_THROW(
      fs.seekWithinSection(
          Pid::lowest(),
          folly::ByteRange(prefix, 2),
          Id::lowest(),
          Id::lowest() + 1,
          restart),
      std::runtime_error);
}

TEST(FactSetTest, SerializeReorderWritesRequestedFactsInRequestedOrder) {
  FactSet fs(Id::lowest());
  unsigned char d1[] = "key1value1";
  unsigned char d2[] = "key2value2";
  unsigned char d3[] = "key3value3";
  fs.define(Pid::lowest(), clauseFrom(d1, 10, 4));
  fs.define(Pid::lowest() + 1, clauseFrom(d2, 10, 4));
  fs.define(Pid::lowest() + 2, clauseFrom(d3, 10, 4));

  const uint64_t order[] = {(Id::lowest() + 2).toWord(), Id::lowest().toWord()};
  const auto serialized = fs.serializeReorder(folly::range(order));

  EXPECT_EQ(serialized.first, Id::lowest());
  EXPECT_EQ(serialized.count, 2);

  binary::Input input(serialized.facts.bytes());
  Pid type = Pid::invalid();
  Fact::Clause clause;
  Fact::deserialize(input, type, clause);
  EXPECT_EQ(type, Pid::lowest() + 2);
  EXPECT_EQ(clause.key().str(), "key3");
  EXPECT_EQ(clause.value().str(), "value3");

  Fact::deserialize(input, type, clause);
  EXPECT_EQ(type, Pid::lowest());
  EXPECT_EQ(clause.key().str(), "key1");
  EXPECT_EQ(clause.value().str(), "value1");
}
