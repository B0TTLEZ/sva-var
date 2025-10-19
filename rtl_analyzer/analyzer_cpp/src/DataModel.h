#pragma once
#include <string>
#include <set>
#include <map>
#include <vector>

struct ConditionClause {
    std::string signal;
    bool polarity;

    bool operator<(const ConditionClause& other) const {
        if (signal != other.signal) return signal < other.signal;
        return polarity < other.polarity;
    }
};

using ConditionPath = std::set<ConditionClause>;

struct AssignmentInfo {
    ConditionPath path;
    std::set<std::string> drivingSignals;
    std::string file;
    int line = 0;
    std::string type = "direct"; // "direct", "port_connection", "constant"

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