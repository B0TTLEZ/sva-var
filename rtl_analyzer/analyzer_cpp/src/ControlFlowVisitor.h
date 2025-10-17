#pragma once

#include <string>
#include <set>
#include <map>
#include <vector>
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/statements/ConditionalStatements.h"

// 存储分析结果的数据结构：Key是被控信号, Value是控制信号集合
using ControlMap = std::map<std::string, std::set<std::string>>;

class ControlFlowVisitor : public slang::ast::ASTVisitor<ControlFlowVisitor, true, true> {
public:
    ControlFlowVisitor() = default;

    template<typename T>
    void handle(const T& node) {
        visitDefault(node);
    }

    void handle(const slang::ast::ConditionalStatement& stmt);
    void handle(const slang::ast::CaseStatement& stmt);

    const ControlMap& getControlMap() const {
        return controlMap;
    }

private:
    ControlMap controlMap;
};