/*
 * File:  abstract_fun_model.h
 * Author:  mikolas
 * Created on:  Wed Jun 7 11:06:24 CEST 2023
 * Copyright (C) 2023, Mikolas Janota
 */
#pragma once
#include <string>

#include "cvc5_private.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;
class Rewriter;
class AbstractFunModel
{
 public:
  virtual ~AbstractFunModel() {}
  virtual void clear() = 0;
  virtual void setValue(TheoryModel* m, Node n, Node v, bool ground = true) = 0;
  virtual void setDefaultValue(TheoryModel* m, Node v) = 0;
  virtual void simplify() = 0;

  /** getFunctionValue for args with set prefix */
  virtual Node getFunctionValue(const std::string& argPrefix, Rewriter* r) = 0;
  virtual void debugPrint( std::ostream& out, TheoryModel* m, int ind = 0 )=0;
};

}  // namespace theory
}  // namespace cvc5::internal
