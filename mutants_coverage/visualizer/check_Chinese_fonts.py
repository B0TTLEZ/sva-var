import matplotlib.font_manager as fm

# 列出所有可用字体
fonts = [f.name for f in fm.fontManager.ttflist]
# 查找中文字体（包含CJK、WenQuanYi、Noto等关键词）
chinese_fonts = [f for f in fonts if any(key in f for key in ["CJK", "WenQuanYi", "Noto"])]
print("Available Chinese fonts:", chinese_fonts)