#pragma once
#include <string>
#include <set>
#include <map>
#include <vector>

// 改进的条件表达式节点
struct ConditionExpression {
    std::string expression;  // 完整的表达式文本
    std::set<std::string> involvedSignals;  // 涉及的所有信号
    
    bool operator<(const ConditionExpression& other) const {
        if (expression != other.expression) 
            return expression < other.expression;
        return involvedSignals < other.involvedSignals;
    }
};

struct ConditionClause {
    ConditionExpression expr;  // 条件表达式
    bool polarity;            // true: 原表达式, false: 取反
    
    bool operator<(const ConditionClause& other) const {
        if (expr < other.expr) return true;
        if (other.expr < expr) return false;
        return polarity < other.polarity;
    }
};

using ConditionPath = std::set<ConditionClause>;

struct AssignmentInfo {
    ConditionPath path;
    std::set<std::string> drivingSignals;
    std::string file;
    int line = 0;
    std::string type = "direct";

    bool operator<(const AssignmentInfo& other) const {
        if (path < other.path) return true;
        if (other.path < path) return false;
        if (drivingSignals < other.drivingSignals) return true;
        if (other.drivingSignals < drivingSignals) return false;
        if (file != other.file) return file < other.file;
        if (line != other.line) return line < other.line;
        return type < other.type;
    }
};

struct VariableInfo {
    std::string fullName;
    std::string type;
    std::string fileName;
    int line = 0;
    std::string direction;
    size_t bitWidth = 0;
    std::set<AssignmentInfo> assignments;
    std::set<std::string> fanOut;
};