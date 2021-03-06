/*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */
#import <Foundation/Foundation.h>

// init dictionary

NSDictionary* nsdictionary_init_literal_constant() {
  NSDictionary* dict =
      @{@"helloString" : @"Hello, World!",
        @"magicNumber" : @42};
  return dict;
}

NSDictionary* nsdictionary_init_dictionary_constant() {
  return [NSDictionary dictionary];
}

void nsdictionary_init_with_dictionary_linear_FP(NSDictionary* dict) {
  NSDictionary* copy_dict = [[NSDictionary alloc] initWithDictionary:dict];
  for (int i = 0; i < [copy_dict allValues].count; i++) {
  }
}

// accessing values and keys

void nsdictionary_all_keys_linear_FP(NSDictionary* dict) {
  for (int i = 0; i < [dict allKeys].count; i++) {
  }
}

void nsdictionary_all_values_linear_FP(NSDictionary* dict) {
  for (int i = 0; i < [dict allValues].count; i++) {
  }
}

// enumerate dictionary

void nsdictionary_fast_enumerate_linear_FN(NSDictionary* dict) {
  for (id key in dict) {
  }
}

void nsdictionary_enumerate_constant() {
  NSDictionary* dict =
      @{@"helloString" : @"Hello, World!",
        @"magicNumber" : @42};

  for (NSString* key in dict) {
    id value = dict[key];
  }
}

void nsdictionary_enumerator_linear_FN(NSDictionary* dict) {
  NSEnumerator* enumerator = [dict keyEnumerator];
  id key;
  while ((key = [enumerator nextObject])) {
  }
}
