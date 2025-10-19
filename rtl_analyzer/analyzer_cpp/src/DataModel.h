#pragma once

#include <string>
#include <set>
#include <map>
#include <vector>

// 这个文件只定义我们项目中共享的数据结构

struct VariableInfo {
    std::string fullName;
    std::string type;
    std::string fileName;
    int line = 0;
    std::string direction;
    size_t bitWidth = 0;
    std::set<std::string> fanInControl;
    std::set<std::string> fanInData;
    std::set<std::string> fanOut;
};

// 我们可以把 ControlMap 也移到这里，因为它也是一个共享的数据类型
using ControlMap = std::map<std::string, std::set<std::string>>;