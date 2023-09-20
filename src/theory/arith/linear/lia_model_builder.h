/*
 * File:  lia_model_builder.h
 * Author:  mikolas
 * Created on:  Wed Jun 7 09:53:20 CEST 2023
 * Copyright (C) 2023, Mikolas Janota
 */
#pragma once
#include <utility>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/abstract_fun_model.h"
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5::internal {
class Env;
namespace theory {

class TheoryModel;
class Rewriter;
namespace arith::linear {

class LiaModelBuilder : public AbstractFunModel, protected EnvObj
{
 public:
  /** Check if the class can handle the given function definition. */
  static bool canHandle(const Node n);

 public:
  LiaModelBuilder(Env& env, Node op, const std::string argPrefix);
  virtual ~LiaModelBuilder() {}
  virtual void clear() override { d_points.clear(); };
  virtual void setValue(TheoryModel* m,
                        Node n,
                        Node v,
                        bool ground = true) override;
  virtual void setDefaultValue(TheoryModel*, Node v) override
  {
    d_default = v;
  };
  virtual void debugPrint(std::ostream& out,
                          TheoryModel* m,
                          int ind = 0) override;

  virtual void simplify() override;

  /** getFunctionValue for args with set prefix */
  virtual Node getFunctionValue(const std::string& argPrefix,
                                Rewriter* r) override;

 public:
  using FunArgs = std::vector<Integer>;
  struct FunPoint
  {
    FunArgs args;
    Node val;
  };

 private:
  /** The function for which we are constructing the body. **/
  const Node d_op;
  /** Prefix for fun args. **/
  const std::string d_argPrefix;
  /** op's type **/
  const TypeNode d_typen;
  /** Default value. **/
  Node d_default;
  /**  This is where we stored the body of the function. **/
  Node d_body;
  /** The arguments of the function. **/
  std::vector<Node> d_vars;
  /** The function points on which we are building.. **/
  std::vector<FunPoint> d_points;

  /** Build function body. **/
  Node buildBodyPred();
  /** Build predicate body. **/
  Node buildBodyFun();

  /** Build unary function body starting at point ix. **/
  Node buildFunGreedyUnary(size_t ix);
  /** Build general function body starting at point ix. **/
  Node buildFunGreedyRec(size_t ix);
  /** Build general pred body starting at point ix. **/
  Node buildPredGreedyRec(size_t ix);

  /** Build predicate based on points in indices. **/
  Node buildPredSmarterRec(const std::vector<size_t>& indices);
  /** Build predicate based on points in indices. **/
  Node buildPredSmarter();
};

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
