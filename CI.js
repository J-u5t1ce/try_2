package com.courseware.translate;

import org.apache.pdfbox.pdmodel.PDDocument;
import org.apache.pdfbox.pdmodel.PDPage;
import org.apache.pdfbox.pdmodel.PDPageContentStream;
import org.apache.pdfbox.pdmodel.PDResources;
import org.apache.pdfbox.pdmodel.font.PDType0Font;
import org.apache.pdfbox.pdmodel.common.PDRectangle;
import org.apache.pdfbox.pdmodel.graphics.PDXObject;
import org.apache.pdfbox.pdmodel.graphics.image.PDImageXObject;
import org.apache.pdfbox.cos.COSName;
import org.apache.pdfbox.pdmodel.interactive.annotation.PDAnnotation;
import org.apache.pdfbox.pdmodel.interactive.annotation.PDAnnotationText;
import org.apache.pdfbox.rendering.PDFRenderer;
import org.apache.pdfbox.rendering.ImageType;
import org.apache.pdfbox.contentstream.PDFGraphicsStreamEngine;
import org.apache.pdfbox.pdmodel.graphics.image.PDImage;
import org.apache.pdfbox.util.Matrix;

import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sourceforge.tess4j.Tesseract;
import net.sourceforge.tess4j.TesseractException;
import net.sourceforge.tess4j.util.ImageHelper;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.io.ByteArrayOutputStream;
import java.io.FilterOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;
import java.util.Locale;
import java.util.TreeMap;
import java.util.Arrays;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.function.BiConsumer;
import java.awt.Rectangle;
import java.awt.image.BufferedImage;
import java.awt.image.RescaleOp;
import java.awt.Graphics2D;
import java.awt.RenderingHints;

public class NotabilityStyleTranslator {

    private static final String CHINESE_FONT_PATH = "C:/Windows/Fonts/simhei.ttf";
    private static final String OUTPUT_DIR = "C:/Users/lenovo/Desktop/fyp_test_pdf/slides_test/";

    // 快速模式开关 - 设置为true可以跳过延迟以提升速度
    private static final boolean FAST_MODE = true;

    // 文本框模式开关 - 设置为true生成可编辑的文本框（适合平板笔记功能）
    private static final boolean TEXTBOX_MODE = false;

    // OCR开关 - 当检测到无文本页面时，使用OCR识别图片中的文字
    private static final boolean ENABLE_OCR = true;

    /**
     * 混合页：当页面既有 PDF 文本层又有嵌入位图时，对整页渲染做 OCR，剔除与文本层重叠的识别结果，
     * 仅翻译「仅在图片中出现」的文字（如幻灯片里的示意图文本框）。
     */
    private static final boolean ENABLE_HYBRID_IMAGE_OCR = true;

    /** 小于此像素面积的嵌入图视为装饰/图标，不触发混合页补充 OCR（减少误触发） */
    private static final long MIN_RASTER_IMAGE_PIXELS = 8000L;

    /**
     * 文本层已有足够正文时，若所有「足够大」的嵌入位图绘制区域均落在页脚/装饰带（如右下角校徽），
     * 则不再做全页混合 OCR，避免校徽反色/抗锯齿把正文再识别一遍。
     */
    private static final int HYBRID_SKIP_DECORATIVE_RASTER_MIN_TEXT_CHARS = 180;

    /** 视为「整页渲染影子词」的混合 OCR 片段最大字符数（过长的仍可能是示意图独有文案） */
    private static final int HYBRID_SHADOW_OCR_MAX_FRAGMENT_LEN = 38;
    /**
     * 影子词排除：OCR 的 Y 明显低于「同一文本层行上能解释全部实词」的最小 Y 时，视为页面上方位图、下方位图说明，
     * 而非矢量字重影（与 {@link #hybridOcrIsRenderedTextShadowOfTextLayer} 共用同一套自上而下坐标语义）。
     */
    private static final float HYBRID_SHADOW_MIN_VERTICAL_SEP_BELOW_TEXT_LAYER_PT = 88f;

    /** 译文放在英文块下方的竖直间距（页面「自顶向下」坐标） */
    private static final float TRANSLATION_PAD_BELOW_TEXT_LAYER = 14.0f;
    private static final float TRANSLATION_PAD_BELOW_OCR = 17.0f;
    /** 行间塞译文时与相邻英文块的上下留白 */
    private static final float TRANSLATION_INTERLINE_GAP_PAD = 13.0f;
    /** 译文避让嵌入示意图/位图区域的额外下移距离 */
    private static final float TRANSLATION_CLEAR_OF_FIGURE_PT = 11.0f;
    /**
     * 旧逻辑：对 Y 做页中轴对称后再下移，易把右侧段落译文「镜像」到左侧盖住图。默认关闭，改为锚定在原文块正下方/同栏行间。
     */
    private static final boolean TRANSLATION_PLACEMENT_USE_AXIS_SYMMETRY = false;
    /** 校名页脚译文字号（避免盖住徽标） */
    private static final float UNIVERSITY_FOOTER_ZH_FONT_SIZE = 6.8f;
    private static final float UNIVERSITY_FOOTER_ZH_LINE_HEIGHT = 9.0f;

    /** 正文中文译文字号与行高（静态绘制 {@link #drawTranslation} 与占位计算共用，原 10pt/12pt 比例保留） */
    private static final float TRANSLATION_ZH_FONT_SIZE_PT = 9.5f;
    private static final float TRANSLATION_ZH_LINE_HEIGHT_PT = 12.0f * TRANSLATION_ZH_FONT_SIZE_PT / 10.0f;

    /** OCR 词框与文本层覆盖矩形重叠面积占词框面积比例超过此值，则认为该词已由文本层提供 */
    private static final double OCR_TEXT_LAYER_OVERLAP_THRESHOLD = 0.35;

    /** Tesseract 页迭代级别：2 = RIL_TEXTLINE（按行取框） */
    private static final int TESS_PAGE_ITERATOR_TEXTLINE = 2;

    /** Tesseract 页迭代级别：3 = RIL_WORD（混合页用：按词框聚行 + 水平大间隙拆分，避免左右两栏被合成一行） */
    private static final int TESS_PAGE_ITERATOR_WORD = 3;

    /** 全局整页 OCR 使用的页面分割模式（与 initializeTesseract 一致） */
    private static final int TESS_DEFAULT_PAGE_SEG_MODE = 11;

    /**
     * 混合页嵌入图补充 OCR 临时使用的 PSM：6 = 假定单一文本块，多行列表结构更稳定
     * （识别结束后会恢复为 {@link #TESS_DEFAULT_PAGE_SEG_MODE}）
     */
    private static final int TESS_HYBRID_EMBEDDED_PAGE_SEG_MODE = 6;

    // OCR DPI设置 - 更高的DPI可以获得更好的识别效果，但处理时间更长
    // 对于包含表格和复杂布局的幻灯片，使用更高的DPI可以提高识别率
    private static final float OCR_DPI = 400.0f;

    // Tesseract OCR实例（延迟初始化）
    private static Tesseract tesseract = null;

    // 静态初始化块：在类加载时立即拦截Java命令输出
    static {
        suppressJavaCommandOutput();
    }

    public static void main(String[] args) {
        // 抑制PDFBox字体解析警告（这些警告不影响功能，但会产生大量红色输出）
        suppressPDFBoxFontWarnings();

        // 测试数字序号拆分功能
        testNumberedItemsSplitting();

        String inputFile = "C:/Users/lenovo/Desktop/fyp_test_pdf/slides_test/mec302_lect05_Embedded_processors.pdf";
        String outputFile = OUTPUT_DIR + "MEC302 week5).pdf";

        try {
            System.out.println("🎨 启动平板笔记风格翻译器...");
            if (TEXTBOX_MODE) {
                System.out.println("📦 文本框模式已启用 - 将生成可在平板笔记应用中编辑的文本框");
            } else {
                System.out.println("📝 静态文本模式 - 将生成固定位置的文本");
            }

            int startPageIndex = 0; // 第 n 页
            int endPageIndex = 36;   // 第 m 页
            translatePDFWithNotabilityStyle(inputFile, outputFile, startPageIndex, endPageIndex);


            System.out.println("✅ 平板笔记风格翻译完成！");
            System.out.println("📄 输出文件: " + outputFile);
            if (TEXTBOX_MODE) {
                System.out.println("📱 请在平板笔记应用中打开PDF，可以自由调整文本框位置和大小");
            }
        } catch (Exception e) {
            System.err.println("❌ 翻译失败: " + e.getMessage());
            e.printStackTrace();
        }
    }


    private static void suppressPDFBoxFontWarnings() {
        // 设置日志级别来抑制PDFBox和FontBox的警告
        try {
            // 尝试使用SLF4J设置日志级别
            org.slf4j.Logger logger = org.slf4j.LoggerFactory.getLogger("org.apache.pdfbox");
            if (logger instanceof ch.qos.logback.classic.Logger) {
                ((ch.qos.logback.classic.Logger) logger).setLevel(ch.qos.logback.classic.Level.ERROR);
            }

            org.slf4j.Logger fontLogger = org.slf4j.LoggerFactory.getLogger("org.apache.fontbox");
            if (fontLogger instanceof ch.qos.logback.classic.Logger) {
                ((ch.qos.logback.classic.Logger) fontLogger).setLevel(ch.qos.logback.classic.Level.ERROR);
            }
        } catch (Exception e) {
            // 如果日志配置失败，使用System.err过滤
            // 保存原始的System.err
            final PrintStream originalErr = System.err;

            // 创建一个过滤后的PrintStream
            PrintStream filteredErr = new PrintStream(new ByteArrayOutputStream()) {
                @Override
                public void println(String x) {
                    // 过滤掉常见的PDFBox字体警告
                    if (x != null && (
                            x.contains("Skip table") ||
                                    x.contains("Could not read embedded OTF") ||
                                    x.contains("Could not load font file") ||
                                    x.contains("'head' table is mandatory") ||
                                    (x.contains("java.io.EOFException") && x.contains("font")) ||
                                    x.contains("org.apache.fontbox") ||
                                    x.contains("org.apache.pdfbox.pdmodel.font")
                    )) {
                        // 静默忽略这些警告
                        return;
                    }
                    // 其他错误正常输出
                    originalErr.println(x);
                }

                @Override
                public void print(String s) {
                    if (s != null && (
                            s.contains("Skip table") ||
                                    s.contains("Could not read embedded OTF") ||
                                    s.contains("Could not load font file") ||
                                    s.contains("'head' table is mandatory") ||
                                    (s.contains("java.io.EOFException") && s.contains("font")) ||
                                    s.contains("org.apache.fontbox") ||
                                    s.contains("org.apache.pdfbox.pdmodel.font")
                    )) {
                        return;
                    }
                    originalErr.print(s);
                }
            };

            // 替换System.err
            System.setErr(filteredErr);
        }
    }

    private static void suppressJavaCommandOutput() {
        try {
            // 保存原始的System.out
            final PrintStream originalOut = System.out;

            // 获取原始的OutputStream
            OutputStream originalOutputStream = originalOut;
            try {
                java.lang.reflect.Field field = PrintStream.class.getDeclaredField("out");
                field.setAccessible(true);
                originalOutputStream = (OutputStream) field.get(originalOut);
            } catch (Exception e) {
                // 如果反射失败，使用默认方式
            }

            // 创建一个过滤后的OutputStream
            FilterOutputStream filteredOutputStream = new FilterOutputStream(originalOutputStream) {
                private StringBuilder buffer = new StringBuilder();

                @Override
                public void write(int b) throws java.io.IOException {
                    // 将字节转换为字符并缓冲
                    if (b == '\n' || b == '\r') {
                        String line = buffer.toString();
                        buffer.setLength(0);

                        // 过滤掉包含Java命令执行信息的行
                        if (!shouldFilter(line)) {
                            // 将整行写入原始输出流
                            byte[] bytes = line.getBytes(java.nio.charset.StandardCharsets.UTF_8);
                            out.write(bytes);
                            out.write(b);
                        }
                    } else {
                        buffer.append((char) b);
                    }
                }

                @Override
                public void write(byte[] b, int off, int len) throws java.io.IOException {
                    String text = new String(b, off, len, java.nio.charset.StandardCharsets.UTF_8);
                    if (!shouldFilter(text)) {
                        out.write(b, off, len);
                    }
                }

                @Override
                public void flush() throws java.io.IOException {
                    // 刷新缓冲区
                    if (buffer.length() > 0) {
                        String line = buffer.toString();
                        buffer.setLength(0);
                        if (!shouldFilter(line)) {
                            byte[] bytes = line.getBytes(java.nio.charset.StandardCharsets.UTF_8);
                            out.write(bytes);
                        }
                    }
                    out.flush();
                }

                private boolean shouldFilter(String text) {
                    if (text == null || text.trim().isEmpty()) {
                        return false;
                    }
                    return text.contains("java.exe") ||
                            text.contains("javaagent") ||
                            text.contains("idea_rt.jar") ||
                            text.contains("-Dfile.encoding") ||
                            text.contains("-Dsun.stdout.encoding") ||
                            text.contains("-Dsun.stderr.encoding") ||
                            text.contains("-classpath") ||
                            text.contains("-javaagent:") ||
                            (text.contains("Program Files") && text.contains("Java")) ||
                            (text.contains("jdk-") && text.contains("bin")) ||
                            (text.startsWith("\"") && text.contains("java.exe"));
                }
            };

            // 创建新的PrintStream并替换System.out
            PrintStream filteredOut = new PrintStream(filteredOutputStream, true);
            System.setOut(filteredOut);
        } catch (Exception e) {
            // 如果过滤失败，使用简单的PrintStream包装
            final PrintStream originalOut = System.out;
            PrintStream filteredOut = new PrintStream(new ByteArrayOutputStream()) {
                @Override
                public void println(String x) {
                    if (x != null && !shouldFilter(x)) {
                        originalOut.println(x);
                    }
                }

                @Override
                public void print(String s) {
                    if (s != null && !shouldFilter(s)) {
                        originalOut.print(s);
                    }
                }

                private boolean shouldFilter(String text) {
                    return text.contains("java.exe") ||
                            text.contains("javaagent") ||
                            text.contains("idea_rt.jar") ||
                            text.contains("-Dfile.encoding") ||
                            text.contains("-Dsun.stdout.encoding") ||
                            text.contains("-Dsun.stderr.encoding") ||
                            text.contains("-classpath") ||
                            text.contains("-javaagent:") ||
                            (text.contains("Program Files") && text.contains("Java")) ||
                            (text.contains("jdk-") && text.contains("bin")) ||
                            (text.startsWith("\"") && text.contains("java.exe"));
                }
            };
            System.setOut(filteredOut);
        }
    }

    /**
     * 测试数字序号拆分功能
     */
    private static void testNumberedItemsSplitting() {
        System.out.println("🧪 测试数字序号拆分功能...");

        // 测试用例1：包含句子内部编号的情况
        String testText1 = "1. A design should exhibit an architecture that (1) has been created using recognizable architectural styles or patterns, (2) is composed of components that exhibit good design characteristics, and (3) can be implemented in an evolutionary fashion, thereby facilitating implementation and testing.";

        List<String> result1 = splitNumberedItems(testText1);
        System.out.println("测试用例1 - 包含内部编号的单个句子:");
        System.out.println("原文: " + testText1);
        System.out.println("拆分结果: " + result1.size() + " 项");
        for (int i = 0; i < result1.size(); i++) {
            System.out.println("  [" + (i+1) + "] " + result1.get(i));
        }
        System.out.println();

        // 测试用例2：多个真正的序号
        String testText2 = "1. A design should exhibit an architecture. 2. A design should be modular. 3. A design should contain distinct representations.";

        List<String> result2 = splitNumberedItems(testText2);
        System.out.println("测试用例2 - 多个真正的序号:");
        System.out.println("原文: " + testText2);
        System.out.println("拆分结果: " + result2.size() + " 项");
        for (int i = 0; i < result2.size(); i++) {
            System.out.println("  [" + (i+1) + "] " + result2.get(i));
        }
        System.out.println();

        // 测试用例3：混合情况
        String testText3 = "1. A design should exhibit an architecture that (1) has been created using recognizable architectural styles or patterns, (2) is composed of components that exhibit good design characteristics, and (3) can be implemented in an evolutionary fashion, thereby facilitating implementation and testing. 2. A design should be modular; that is, the software should be logically partitioned into elements or subsystems.";

        List<String> result3 = splitNumberedItems(testText3);
        System.out.println("测试用例3 - 混合情况:");
        System.out.println("原文: " + testText3);
        System.out.println("拆分结果: " + result3.size() + " 项");
        for (int i = 0; i < result3.size(); i++) {
            System.out.println("  [" + (i+1) + "] " + result3.get(i));
        }
        System.out.println();
    }

    /**
     * 翻译整个 PDF（全部页码）。等价于 translatePDFWithNotabilityStyle(inputPath, outputPath, null, null)。
     */
    public static void translatePDFWithNotabilityStyle(String inputPath, String outputPath) throws Exception {
        translatePDFWithNotabilityStyle(inputPath, outputPath, null, null);
    }

    /**
     * 按页码范围翻译 PDF。
     * @param inputPath  输入 PDF 路径
     * @param outputPath 输出 PDF 路径
     * @param startPage  起始页（0-based），null 表示从第 1 页开始
     * @param endPage    结束页（0-based），null 表示到最后一页
     */
    public static void translatePDFWithNotabilityStyle(String inputPath, String outputPath, Integer startPage, Integer endPage) throws Exception {
        translatePDFWithNotabilityStyle(inputPath, outputPath, startPage, endPage, null);
    }

    /**
     * 按页码范围翻译 PDF，支持进度回调（每处理完一页调用一次）。
     * @param progressCallback 回调 (currentPage1Based, totalPages)，可为 null
     */
    public static void translatePDFWithNotabilityStyle(String inputPath, String outputPath, Integer startPage, Integer endPage, BiConsumer<Integer, Integer> progressCallback) throws Exception {
        translatePDFWithNotabilityStyle(inputPath, outputPath, startPage, endPage, null, progressCallback);
    }

    /**
     * 按页码范围或指定页集合翻译 PDF。当 selectedPages 非 null 时仅处理该集合中的页（0-based）。
     */
    public static void translatePDFWithNotabilityStyle(String inputPath, String outputPath, Integer startPage, Integer endPage, Set<Integer> selectedPages, BiConsumer<Integer, Integer> progressCallback) throws Exception {
        try (PDDocument document = PDDocument.load(new File( inputPath))) {

            // 加载中文字体
            PDType0Font chineseFont = PDType0Font.load(document, new File(CHINESE_FONT_PATH));

            int totalPages = document.getNumberOfPages();
            int maxPageIndex = totalPages - 1;
            System.out.println("🔍 开始处理，PDF 共 " + totalPages + " 页");

            int start = (startPage != null) ? startPage : 0;
            int end = (endPage != null) ? endPage : maxPageIndex;

            // 检查并调整页码范围，确保不超出PDF的实际页数
            if (start < 0) {
                System.out.println("⚠️ 起始页码小于0，调整为0");
                start = 0;
            }
            if (end > maxPageIndex) {
                System.out.println("⚠️ 结束页码 " + (end + 1) + " 超出PDF总页数 " + totalPages + "，调整为 " + (maxPageIndex + 1));
                end = maxPageIndex;
            }
            if (start > end) {
                System.out.println("⚠️ 起始页码大于结束页码，调整为只处理第" + (start + 1) + "页");
                end = start;
            }

            final int startPageFinal = start;
            final int endPageFinal = end;
            final int totalPagesToProcess = (selectedPages != null) ? selectedPages.size() : (endPageFinal - startPageFinal + 1);
            System.out.println("[PAGES] Processing page range: " + (startPageFinal + 1) + " to " + (endPageFinal + 1) + " (1-based), total " + totalPagesToProcess + " pages. PDF total pages: " + totalPages);
            System.out.println("📄 处理第" + (startPageFinal + 1) + "页到第" + (endPageFinal + 1) + "页，共" + totalPagesToProcess + "页");

            // 记录翻译开始时间
            long startTime = System.currentTimeMillis();
            final int[] processedCount = { 0 };

            for (int pageIndex = startPageFinal; pageIndex <= endPageFinal; pageIndex++) {
                if (selectedPages != null && !selectedPages.contains(pageIndex)) continue;

                // 计算当前进度（范围模式用序号，指定页模式用 processedCount）
                int currentPage = (selectedPages != null) ? (processedCount[0] + 1) : (pageIndex - startPageFinal + 1);

                // 添加边界检查，防止索引超出范围
                if (pageIndex < 0 || pageIndex >= totalPages) {
                    System.out.println("⚠️ 页面索引 " + pageIndex + " 超出范围（总页数: " + totalPages + "），跳过");
                    showProgressBar(currentPage, totalPagesToProcess);
                    if (progressCallback != null) {
                        if (selectedPages != null) processedCount[0]++;
                        progressCallback.accept(selectedPages != null ? processedCount[0] : currentPage, totalPagesToProcess);
                    }
                    continue;
                }

                PDPage page;
                try {
                    page = document.getPage(pageIndex);
                } catch (IndexOutOfBoundsException e) {
                    System.out.println("⚠️ 页面 " + (pageIndex + 1) + " 不存在，跳过（总页数: " + totalPages + "）");
                    showProgressBar(currentPage, totalPagesToProcess);
                    if (progressCallback != null) {
                        if (selectedPages != null) processedCount[0]++;
                        progressCallback.accept(selectedPages != null ? processedCount[0] : currentPage, totalPagesToProcess);
                    }
                    continue;
                }

                System.out.println("\n📄 处理第" + (pageIndex + 1) + "页...");

                // 为当前页单独提取文本
                List<CoordinateTextStripper.TextItem> textItems;
                boolean mainPassOcrMode = false; // 主流程是否整页 OCR（无文本层时）

                // 首先尝试普通文本提取
                CoordinateTextStripper stripper = new CoordinateTextStripper();
                stripper.setStartPage(pageIndex + 1);
                stripper.setEndPage(pageIndex + 1);
                stripper.getText(document);
                textItems = new ArrayList<>(stripper.textItems);

                // 判断页面类型
                if (textItems.isEmpty()) {
                    System.out.println("📷 检测到图片形式的PDF页面（无文本层），将使用OCR识别");
                } else {
                    System.out.println("📝 检测到文本形式的PDF页面（有文本层），使用文本提取");
                }

                // 如果页面没有文本且启用了OCR，使用OCR识别（与普通文本提取方式一致）
                if (textItems.isEmpty() && ENABLE_OCR) {
                    try {
                        System.out.println("🔍 开始OCR识别...");
                        textItems = extractTextWithOCR(document, page, pageIndex);
                        mainPassOcrMode = true; // 标记为OCR模式
                        System.out.println("✅ OCR识别完成，找到 " + textItems.size() + " 个文本项");
                    } catch (Exception e) {
                        System.err.println("❌ OCR识别失败: " + e.getMessage());
                        e.printStackTrace();
                    }
                } else if (textItems.isEmpty() && !ENABLE_OCR) {
                    System.out.println("⚠️ OCR功能已禁用，无法识别图片形式的PDF页面");
                }

                // 混合页：有文本层且存在足够大的嵌入位图时，补充 OCR 仅保留「非文本层」区域
                List<CoordinateTextStripper.TextItem> imageSupplementItems = new ArrayList<>();
                if (!textItems.isEmpty() && ENABLE_OCR && ENABLE_HYBRID_IMAGE_OCR && !mainPassOcrMode) {
                    try {
                        if (pageHasRasterImages(page)) {
                            if (shouldSkipHybridOcrForDecorativeEmbeddedRastersOnly(page, textItems)) {
                                System.out.println("🔀 混合页面：嵌入大图仅位于页脚/装饰区（如校徽），跳过全页补充 OCR");
                            } else {
                                System.out.println("🔀 混合页面：检测到嵌入位图，将对图片内文字补充 OCR（剔除与文本层重叠部分）...");
                                imageSupplementItems = extractImageEmbeddedTextViaOCR(document, page, pageIndex, textItems);
                                if (!imageSupplementItems.isEmpty()) {
                                    System.out.println("✅ 图片补充 OCR 得到 " + imageSupplementItems.size() + " 个文本项，将单独翻译并绘制在对应位置下方");
                                } else {
                                    System.out.println("ℹ️ 图片补充 OCR 未得到额外可译文本（或全部被文本层覆盖）");
                                }
                            }
                        }
                    } catch (Exception e) {
                        System.err.println("⚠️ 混合页图片 OCR 失败: " + e.getMessage());
                    }
                }

                // 如果仍然没有文本，跳过此页
                if ((textItems == null || textItems.isEmpty()) && imageSupplementItems.isEmpty()) {
                    System.out.println("⚠️ 页面 " + (pageIndex + 1) + " 无文本内容，跳过");
                    showProgressBar(currentPage, totalPagesToProcess);
                    if (progressCallback != null) {
                        if (selectedPages != null) processedCount[0]++;
                        progressCallback.accept(selectedPages != null ? processedCount[0] : currentPage, totalPagesToProcess);
                    }
                    continue;
                }

                System.out.println("📄 页面 " + (pageIndex + 1) + " 找到 " + textItems.size() + " 个文本块" +
                        (mainPassOcrMode ? " (OCR模式)" : " (文本层模式)"));

                // 创建副本文本项列表用于调试输出（不修改原始列表）
                List<CoordinateTextStripper.TextItem> sortedForDebug = new ArrayList<>(textItems);
                // 检测坐标系方向并排序（与groupTextByYCoordinate中的逻辑一致）
                sortedForDebug.sort((a, b) -> Float.compare(a.y, b.y));
                if (!sortedForDebug.isEmpty() && sortedForDebug.size() > 1) {
                    float firstY = sortedForDebug.get(0).y;
                    float lastY = sortedForDebug.get(sortedForDebug.size() - 1).y;
                    if (firstY < lastY) {
                        // 反向坐标系（Y值小在上），保持升序排序
                        // 已经是升序排序，不需要改变
                    } else {
                        // 标准PDFBox坐标系（Y值大在上），使用降序排序
                        sortedForDebug.sort((a, b) -> Float.compare(b.y, a.y));
                    }
                }

                // 打印原始文本项的坐标（按Y坐标从上到下排序）
                System.out.println("🔍 原始文本项坐标（按Y坐标从上到下排序）：");
                for (int i = 0; i < sortedForDebug.size(); i++) {
                    CoordinateTextStripper.TextItem item = sortedForDebug.get(i);
                    System.out.println("  [" + i + "] Y=" + item.y + " -> " + item.text);
                }

                // 处理当前页（文本层或整页 OCR）
                if (!textItems.isEmpty()) {
                    processPageWithNotabilityStyle(document, page, textItems, chineseFont, pageIndex, mainPassOcrMode, false);
                }
                // 嵌入图片中的文字：第二遍使用 OCR 坐标逻辑绘制译文
                if (!imageSupplementItems.isEmpty()) {
                    processPageWithNotabilityStyle(document, page, imageSupplementItems, chineseFont, pageIndex, true, true);
                }

                // 显示进度条
                showProgressBar(currentPage, totalPagesToProcess);
                if (progressCallback != null) {
                    if (selectedPages != null) processedCount[0]++;
                    progressCallback.accept(selectedPages != null ? processedCount[0] : currentPage, totalPagesToProcess);
                }
            }

            // 保存文档
            document.save(outputPath);
            System.out.println("💾 已保存平板笔记风格PDF: " + outputPath);

            // 计算并显示总时间
            long endTime = System.currentTimeMillis();
            long totalTime = endTime - startTime;
            displayTimeStatistics(totalTime, totalPagesToProcess);
        }
    }

    /**
     * 显示翻译进度条
     * @param currentPage 当前已处理的页数
     * @param totalPages 总页数
     */
    private static void showProgressBar(int currentPage, int totalPages) {
        int barLength = 50; // 进度条长度
        int filled = (int) ((double) currentPage / totalPages * barLength);
        int empty = barLength - filled;

        StringBuilder progressBar = new StringBuilder();
        progressBar.append("\r[");
        for (int i = 0; i < filled; i++) {
            progressBar.append("=");
        }
        for (int i = 0; i < empty; i++) {
            progressBar.append(" ");
        }
        progressBar.append("] ");
        progressBar.append(String.format("%d/%d (%.1f%%)", currentPage, totalPages, (double) currentPage / totalPages * 100));

        System.out.print(progressBar.toString());
        if (currentPage == totalPages) {
            System.out.println(); // 完成后换行
        }
    }

    /**
     * 显示时间统计信息
     * @param totalTimeMillis 总时间（毫秒）
     * @param totalPages 总页数
     */
    private static void displayTimeStatistics(long totalTimeMillis, int totalPages) {
        long totalSeconds = totalTimeMillis / 1000;
        long hours = totalSeconds / 3600;
        long minutes = (totalSeconds % 3600) / 60;
        long seconds = totalSeconds % 60;
        long milliseconds = totalTimeMillis % 1000;

        System.out.println("\n⏱️ 翻译时间统计:");
        if (hours > 0) {
            System.out.println(String.format("   总时间: %d小时 %d分钟 %d秒 %d毫秒", hours, minutes, seconds, milliseconds));
        } else if (minutes > 0) {
            System.out.println(String.format("   总时间: %d分钟 %d秒 %d毫秒", minutes, seconds, milliseconds));
        } else {
            System.out.println(String.format("   总时间: %d秒 %d毫秒", seconds, milliseconds));
        }

        if (totalPages > 0) {
            double avgTimePerPage = (double) totalTimeMillis / totalPages;
            System.out.println(String.format("   平均每页: %.2f秒", avgTimePerPage / 1000.0));
        }
    }

    /** 页面自顶向下的矩形（top &lt; bottom），用于避让嵌入图 */
    private static final class LayoutRectTopDown {
        final float left;
        final float top;
        final float right;
        final float bottom;

        LayoutRectTopDown(float l, float t, float r, float b) {
            left = l;
            top = t;
            right = r;
            bottom = b;
        }
    }

    private static List<LayoutRectTopDown> buildLayoutFigureExclusionTopDown(PDPage page, float pageHeight) {
        List<LayoutRectTopDown> out = new ArrayList<>();
        try {
            for (Rectangle2D.Float r : collectLargeEmbeddedImageBoundsInPageSpace(page)) {
                float padX = 8f;
                float padY = 10f;
                float left = (float) r.getMinX() - padX;
                float right = (float) r.getMaxX() + padX;
                float topPdf = (float) r.getMaxY();
                float botPdf = (float) r.getMinY();
                float topTd = pageHeight - topPdf - padY;
                float botTd = pageHeight - botPdf + padY;
                if (right > left && botTd > topTd) {
                    out.add(new LayoutRectTopDown(left, topTd, right, botTd));
                }
            }
        } catch (Exception ignored) {
            // 忽略
        }
        return out;
    }

    private static float textBlockTopFromPageTop(float groupY, float groupBottomY, boolean isMultiline,
                                                 boolean isReversedCoordinate, float pageHeight, float singleLineH) {
        if (isMultiline) {
            if (isReversedCoordinate) {
                return Math.min(groupY, groupBottomY);
            }
            return pageHeight - Math.max(groupY, groupBottomY);
        }
        if (isReversedCoordinate) {
            return groupY;
        }
        return pageHeight - groupY;
    }

    private static float textBlockBottomFromPageTop(float groupY, float groupBottomY, boolean isMultiline,
                                                    boolean isReversedCoordinate, float pageHeight, float singleLineH) {
        if (isMultiline) {
            if (isReversedCoordinate) {
                return Math.max(groupY, groupBottomY);
            }
            return pageHeight - Math.min(groupY, groupBottomY);
        }
        return textBlockTopFromPageTop(groupY, groupBottomY, false, isReversedCoordinate, pageHeight, singleLineH)
                + singleLineH;
    }

    private static float groupHorizontalMin(List<CoordinateTextStripper.TextItem> group) {
        float m = Float.MAX_VALUE;
        for (CoordinateTextStripper.TextItem it : group) {
            if (it != null) {
                m = Math.min(m, it.x);
            }
        }
        return m == Float.MAX_VALUE ? 0f : m;
    }

    private static float groupHorizontalMax(List<CoordinateTextStripper.TextItem> group) {
        float m = Float.NEGATIVE_INFINITY;
        for (CoordinateTextStripper.TextItem it : group) {
            if (it != null) {
                m = Math.max(m, it.x + it.text.length() * 6f);
            }
        }
        return m == Float.NEGATIVE_INFINITY ? 0f : m;
    }

    private static float horizontalSpanOverlap(float a0, float a1, float b0, float b1) {
        float l = Math.max(a0, b0);
        float r = Math.min(a1, b1);
        return Math.max(0f, r - l);
    }

    /**
     * 找「同栏」的下一个文本组，避免用另一栏的行高当作行间空白参考，导致译文挤进图或错位。
     */
    private static int findNextTextGroupIndexInSameColumn(
            List<List<CoordinateTextStripper.TextItem>> textGroups, int groupIndex, float pageWidth) {
        if (groupIndex + 1 >= textGroups.size()) {
            return -1;
        }
        float c0 = groupHorizontalMin(textGroups.get(groupIndex));
        float c1 = groupHorizontalMax(textGroups.get(groupIndex));
        float cw = Math.max(1f, c1 - c0);
        for (int j = groupIndex + 1; j < textGroups.size(); j++) {
            List<CoordinateTextStripper.TextItem> g = textGroups.get(j);
            float g0 = groupHorizontalMin(g);
            float g1 = groupHorizontalMax(g);
            float gw = Math.max(1f, g1 - g0);
            float ov = horizontalSpanOverlap(c0, c1, g0, g1);
            if (ov >= Math.min(cw, gw) * 0.17f) {
                return j;
            }
            if (pageWidth > 10f) {
                boolean curLeft = c1 <= pageWidth * 0.46f;
                boolean curRight = c0 >= pageWidth * 0.50f;
                boolean njLeft = g1 <= pageWidth * 0.46f;
                boolean njRight = g0 >= pageWidth * 0.50f;
                if ((curLeft && njLeft) || (curRight && njRight)) {
                    return j;
                }
            }
        }
        return -1;
    }

    private static float groupTopYFromPageTop(List<CoordinateTextStripper.TextItem> group,
                                              boolean isReversedCoordinate, float pageHeight) {
        if (group == null || group.isEmpty()) {
            return -1f;
        }
        if (isReversedCoordinate) {
            float y = Float.MAX_VALUE;
            for (CoordinateTextStripper.TextItem item : group) {
                y = Math.min(y, item.y);
            }
            return y;
        }
        float y = Float.NEGATIVE_INFINITY;
        for (CoordinateTextStripper.TextItem item : group) {
            y = Math.max(y, item.y);
        }
        return pageHeight - y;
    }

    private static float nudgeTranslationTopClearFigureOverlap(
            float left, float top, float right, float bottom, List<LayoutRectTopDown> figures) {
        if (figures == null || figures.isEmpty()) {
            return top;
        }
        float t = top;
        float h = Math.max(1f, bottom - top);
        for (int iter = 0; iter < 60; iter++) {
            float b = t + h;
            boolean hit = false;
            for (LayoutRectTopDown f : figures) {
                if (right <= f.left || left >= f.right || b <= f.top || t >= f.bottom) {
                    continue;
                }
                t = f.bottom + TRANSLATION_CLEAR_OF_FIGURE_PT;
                hit = true;
                break;
            }
            if (!hit) {
                break;
            }
        }
        return t;
    }

    private static boolean isLikelyUniversityFooterEnglish(String english) {
        if (english == null) {
            return false;
        }
        String e = english.toLowerCase(Locale.ROOT);
        return (e.contains("jiaotong") && e.contains("liverpool"))
                || english.contains("西交利物浦");
    }

    /**
     * 使用平板笔记风格处理单页
     * 生成的PDF可以在平板笔记应用中打开，效果更好
     * @param isOCRMode 是否使用OCR模式（影响坐标处理）
     * @param hybridEmbeddedImageOcrPass 混合页第二遍：嵌入图补充 OCR。为 true 时不做「多行合并成一句」、不调用 DeepSeek 文本质量过滤，
     *                                   尽量保持每条 OCR 行为独立翻译单元（如幻灯片绿色框内多行要点）。
     */
    private static void processPageWithNotabilityStyle(PDDocument document, PDPage page,
                                                       List<CoordinateTextStripper.TextItem> textItems,
                                                       PDType0Font chineseFont, int pageIndex, boolean isOCRMode,
                                                       boolean hybridEmbeddedImageOcrPass) throws Exception {

        float pageWidth = page.getMediaBox().getWidth();
        float pageHeight = page.getMediaBox().getHeight();
        System.out.println("📐 页面尺寸: 宽度=" + pageWidth + ", 高度=" + pageHeight);
        List<LayoutRectTopDown> layoutFigureExclusion = buildLayoutFigureExclusionTopDown(page, pageHeight);

        try (PDPageContentStream contentStream = new PDPageContentStream(document, page,
                PDPageContentStream.AppendMode.APPEND, true, true)) {

            // 将文本项按Y坐标分组（相近的Y坐标归为一组）
            // 同时检测坐标系方向
            // OCR模式和文本层模式的坐标系统可能不同，需要分别处理
            boolean isReversedCoordinate = detectCoordinateSystem(textItems);

            // 对于OCR模式，坐标系统通常是反向的（Y值小在上）
            // 对于文本层模式，坐标系统通常是标准的PDFBox坐标系（Y值大在上）
            // 但需要根据实际检测结果来调整
            if (isOCRMode) {
                // OCR模式：通常使用反向坐标系，但如果检测到标准坐标系，则使用标准坐标系
                // 这里保持检测结果，但可能需要调整排序逻辑
                System.out.println("  [DEBUG] OCR模式，检测到的坐标系: " + (isReversedCoordinate ? "反向" : "标准"));
            } else {
                System.out.println("  [DEBUG] 文本层模式，检测到的坐标系: " + (isReversedCoordinate ? "反向" : "标准"));
            }
            if (hybridEmbeddedImageOcrPass) {
                System.out.println("  [混合OCR] 嵌入图补充模式：禁用多行句合并 + 跳过 DeepSeek OCR 质量过滤，按行独立翻译");
            }

            List<List<CoordinateTextStripper.TextItem>> textGroups = groupTextByYCoordinate(
                    textItems, isReversedCoordinate, isOCRMode, pageWidth, hybridEmbeddedImageOcrPass);

            System.out.println("🎨 页面 " + (pageIndex + 1) + " 分组为 " + textGroups.size() + " 个文本组");

            // 调试输出：显示文本组的顺序
            System.out.println("  [DEBUG 文本组顺序]");
            for (int i = 0; i < textGroups.size(); i++) {
                List<CoordinateTextStripper.TextItem> group = textGroups.get(i);
                StringBuilder groupText = new StringBuilder();
                float groupTopY;
                if (isReversedCoordinate) {
                    groupTopY = Float.MAX_VALUE;
                    for (CoordinateTextStripper.TextItem item : group) {
                        groupTopY = Math.min(groupTopY, item.y);
                        groupText.append(item.text).append(" ");
                    }
                } else {
                    groupTopY = Float.NEGATIVE_INFINITY;
                    for (CoordinateTextStripper.TextItem item : group) {
                        groupTopY = Math.max(groupTopY, item.y);
                        groupText.append(item.text).append(" ");
                    }
                }
                System.out.println("    [" + i + "] Y=" + groupTopY + " -> \"" + groupText.toString().trim() + "\"");
            }

            System.out.println("⚡ 开始快速翻译模式...");

            // 先用规则标记哪些组主要为代码段（用于混合页：只跳过代码组，保留讲解+代码混合段的翻译）
            java.util.Set<Integer> codeSegmentGroupIndices = new java.util.HashSet<>();
            // 公式/数字符号组：不翻译且不放入翻译件，直接跳过
            java.util.Set<Integer> formulaSegmentGroupIndices = new java.util.HashSet<>();
            List<String> aiCodeDetectCandidates = new ArrayList<>();
            List<Integer> aiCodeDetectIndices = new ArrayList<>();
            for (int i = 0; i < textGroups.size(); i++) {
                List<CoordinateTextStripper.TextItem> group = textGroups.get(i);
                StringBuilder sb = new StringBuilder();
                for (CoordinateTextStripper.TextItem item : group) {
                    sb.append(item.text).append(" ");
                }
                String groupText = cleanOCRText(sb.toString().trim());
                if (groupText.isEmpty()) continue;
                if (isLikelyMathOrFormula(groupText)
                        || (hybridEmbeddedImageOcrPass && isLikelyFsmDiagramOrLogicOcrNoise(groupText))) {
                    formulaSegmentGroupIndices.add(i);
                }
                if (isLikelyCodeSegment(groupText)) {
                    codeSegmentGroupIndices.add(i);
                } else {
                    // 规则不明显的文本，交给 DeepSeek 进一步判断是否为代码
                    aiCodeDetectCandidates.add(groupText);
                    aiCodeDetectIndices.add(i);
                }
            }

            // 使用 DeepSeek 智能检测哪些组是代码（可选增强，需配置 DeepSeek）
            if (!aiCodeDetectCandidates.isEmpty() && TranslationConfig.isDeepSeekConfigured()) {
                try {
                    System.out.println("🔍 使用 DeepSeek 检测代码段，候选组数: " + aiCodeDetectCandidates.size());
                    List<Boolean> codeFlags = detectCodeSegmentsWithDeepSeek(aiCodeDetectCandidates);
                    for (int j = 0; j < codeFlags.size() && j < aiCodeDetectIndices.size(); j++) {
                        if (Boolean.TRUE.equals(codeFlags.get(j))) {
                            int idx = aiCodeDetectIndices.get(j);
                            codeSegmentGroupIndices.add(idx);
                        }
                    }
                } catch (Exception e) {
                    System.out.println("⚠️ DeepSeek 代码段检测失败，退回规则检测: " + e.getMessage());
                }
            }
            if (!codeSegmentGroupIndices.isEmpty()) {
                System.out.println("📋 检测到 " + codeSegmentGroupIndices.size() + " 个主要为代码的文本组，将不翻译这些组");
            }
            if (!formulaSegmentGroupIndices.isEmpty()) {
                System.out.println("📐 检测到 " + formulaSegmentGroupIndices.size() + " 个公式/数字符号组，将不翻译且不放入翻译件");
            }

            boolean isCodePage = isLikelyCodePage(textGroups, codeSegmentGroupIndices);
            if (isCodePage) {
                System.out.println("📋 当前页绝大部分为代码，整页跳过翻译与绘制");
            } else {

                // 收集所有需要翻译的文本（跳过主要为代码的组、公式/数字符号组）
                List<String> textsToTranslate = new ArrayList<>();
                List<Integer> textGroupIndices = new ArrayList<>(); // 记录每个文本对应的文本组索引
                for (int i = 0; i < textGroups.size(); i++) {
                    if (codeSegmentGroupIndices.contains(i)) continue; // 代码组不加入翻译列表
                    if (formulaSegmentGroupIndices.contains(i)) continue; // 公式组不翻译且不放入翻译件
                    List<CoordinateTextStripper.TextItem> group = textGroups.get(i);
                    StringBuilder englishText = new StringBuilder();
                    for (CoordinateTextStripper.TextItem item : group) {
                        englishText.append(item.text).append(" ");
                    }
                    String english = englishText.toString().trim();
                    english = cleanOCRText(english);
                    if (!english.isEmpty() && english.length() >= 2) {
                        List<String> corruptedNewlineItems = splitCorruptedNewlineItems(english);
                        boolean addedAnyTranslatable = false;
                        for (String item : corruptedNewlineItems) {
                            if (item.isEmpty() || item.length() < 2) continue;
                            if (isLikelyMathOrFormula(item)) continue;
                            if (hybridEmbeddedImageOcrPass && isLikelyFsmDiagramOrLogicOcrNoise(item)) continue;
                            textsToTranslate.add(item);
                            textGroupIndices.add(i);
                            addedAnyTranslatable = true;
                        }
                        // 整组实为公式碎片但未在第一轮标出时，仍不送翻译、不绘制
                        if (!addedAnyTranslatable) {
                            formulaSegmentGroupIndices.add(i);
                        }
                    }
                }

                // OCR模式：使用本地预过滤和DeepSeek批量检测文本质量，过滤无意义的乱码文本
                // 混合页嵌入图补充 OCR：只做本地预过滤，避免 DeepSeek 把校名、定义句等误判为乱码
                Set<Integer> validTextIndices = new HashSet<>(); // 记录有效的文本索引
                if (isOCRMode && textsToTranslate.size() > 0) {
                    // 第一步：本地预过滤，快速过滤明显的乱码
                    System.out.println("🔍 本地预过滤：快速过滤明显的OCR乱码...");
                    List<String> preFilteredTexts = new ArrayList<>();
                    List<Integer> preFilteredIndices = new ArrayList<>();
                    for (int i = 0; i < textsToTranslate.size(); i++) {
                        String text = textsToTranslate.get(i);
                        // 混合嵌入图：额外识别状态图/逻辑式 OCR（up^¬down、|1|2 等），避免送入翻译污染 PDF
                        boolean gar = isLikelyGarbageText(text);
                        boolean diagramNoise = hybridEmbeddedImageOcrPass && isLikelyFsmDiagramOrLogicOcrNoise(text);
                        boolean dropAsGarbage = (!hybridEmbeddedImageOcrPass && gar)
                                || (hybridEmbeddedImageOcrPass && (gar || diagramNoise));
                        if (dropAsGarbage) {
                            int groupIndex = textGroupIndices.get(i);
                            String reason = diagramNoise && !gar ? "示意图/逻辑式 OCR，不翻译" : "明显乱码";
                            System.out.println("  [本地预过滤] " + reason + " [" + (groupIndex + 1) + "]: \"" +
                                    text.substring(0, Math.min(50, text.length())) + "...\"");
                        } else {
                            preFilteredTexts.add(text);
                            preFilteredIndices.add(textGroupIndices.get(i));
                        }
                    }

                    System.out.println("  [本地预过滤] 过滤了 " + (textsToTranslate.size() - preFilteredTexts.size()) +
                            " 个明显乱码，剩余 " + preFilteredTexts.size() + " 个文本" +
                            (hybridEmbeddedImageOcrPass ? "（混合嵌入图模式：跳过 DeepSeek 质量检测）" : "待DeepSeek检测"));

                    // 第二步：使用DeepSeek检测剩余文本的质量（混合嵌入图 OCR 跳过，保留多行要点）
                    if (!hybridEmbeddedImageOcrPass && preFilteredTexts.size() > 0 && TranslationConfig.isDeepSeekConfigured()) {
                        try {
                            System.out.println("🔍 使用DeepSeek检测文本质量，进一步过滤无意义的OCR乱码...");
                            List<Boolean> textQualityResults = detectTextQualityWithDeepSeek(preFilteredTexts);

                            // 记录有效的文本索引
                            for (int i = 0; i < textQualityResults.size(); i++) {
                                if (textQualityResults.get(i)) {
                                    validTextIndices.add(preFilteredIndices.get(i));
                                } else {
                                    int groupIndex = preFilteredIndices.get(i);
                                    System.out.println("  [DeepSeek检测] 过滤无意义文本 [" + (groupIndex + 1) + "]: \"" +
                                            preFilteredTexts.get(i).substring(0, Math.min(50, preFilteredTexts.get(i).length())) + "...\"");
                                }
                            }

                            // 过滤掉无意义的文本
                            List<String> filteredTexts = new ArrayList<>();
                            List<Integer> filteredIndices = new ArrayList<>();
                            for (int i = 0; i < preFilteredTexts.size(); i++) {
                                if (textQualityResults.get(i)) {
                                    filteredTexts.add(preFilteredTexts.get(i));
                                    filteredIndices.add(preFilteredIndices.get(i));
                                }
                            }
                            textsToTranslate = filteredTexts;
                            textGroupIndices = filteredIndices;

                            System.out.println("✅ 文本质量检测完成，保留 " + textsToTranslate.size() + " 个有效文本");
                        } catch (Exception e) {
                            System.out.println("⚠️ DeepSeek文本质量检测失败，使用本地预过滤结果: " + e.getMessage());
                            // 检测失败时，使用本地预过滤的结果
                            textsToTranslate = preFilteredTexts;
                            textGroupIndices = preFilteredIndices;
                            for (int i = 0; i < preFilteredIndices.size(); i++) {
                                validTextIndices.add(preFilteredIndices.get(i));
                            }
                        }
                    } else {
                        // DeepSeek未配置，或混合嵌入图模式：使用本地预过滤的结果
                        textsToTranslate = preFilteredTexts;
                        textGroupIndices = preFilteredIndices;
                        for (int i = 0; i < preFilteredIndices.size(); i++) {
                            validTextIndices.add(preFilteredIndices.get(i));
                        }
                        System.out.println("✅ 文本质量检测完成（仅本地预过滤），保留 " + textsToTranslate.size() + " 个有效文本");
                    }
                } else {
                    // 非OCR模式，保留所有文本
                    for (int i = 0; i < textsToTranslate.size(); i++) {
                        validTextIndices.add(i);
                    }
                }

                // 批量翻译（优化：优先使用DeepSeek，然后DeepL，最后回退到并行单个翻译）
                List<String> translatedTexts = new ArrayList<>();
                if (textsToTranslate.size() > 0) {
                    // 统计高频英文词（覆盖批量翻译分支）
                    for (String t : textsToTranslate) {
                        observeEnglishTextForGlossary(t);
                    }
                    try {
                        translatedTexts = translateBatchWithDeepSeek(textsToTranslate, "en", "zh");
                    } catch (Exception e) {
                        // DeepSeek批量翻译失败，尝试DeepL
                        try {
                            translatedTexts = translateBatchWithDeepL(textsToTranslate, "en", "zh");
                        } catch (Exception e2) {
                            // 批量翻译失败，使用并行翻译大幅提升速度
                            System.out.println("⚠️ 批量翻译失败，使用并行翻译 (" + textsToTranslate.size() + " 个文本): " + e2.getMessage());
                            translatedTexts = translateParallel(textsToTranslate, "en", "zh");
                            System.out.println("✅ 并行翻译完成，共 " + translatedTexts.size() + " 个结果");
                        }
                    }
                }

                // 遍历所有文本组进行绘制
                int textsToTranslateIndex = 0; // 用于跟踪textsToTranslate的索引

                // 跟踪已绘制的译文位置，用于检测Y坐标冲突
                // 存储格式：{Y坐标, X坐标范围结束位置}
                List<float[]> drawnTranslations = new ArrayList<>(); // [Y坐标, X结束位置]

                for (int groupIndex = 0; groupIndex < textGroups.size(); groupIndex++) {
                    List<CoordinateTextStripper.TextItem> group = textGroups.get(groupIndex);

                    // 主要为代码的组不翻译（混合页中只跳过代码组，讲解+代码混合段会翻译）
                    if (codeSegmentGroupIndices.contains(groupIndex)) {
                        System.out.println("  [跳过] 文本组 [" + (groupIndex + 1) + "] 主要为代码，不翻译");
                        continue;
                    }
                    // 公式/数字符号组：不翻译且不放入翻译件，直接跳过
                    if (formulaSegmentGroupIndices.contains(groupIndex)) {
                        System.out.println("  [跳过] 文本组 [" + (groupIndex + 1) + "] 为公式/数字符号，不翻译且不放置");
                        continue;
                    }

                    // OCR模式：检查该文本组是否被过滤（无意义的乱码）
                    if (isOCRMode) {
                        // 检查这个文本组是否在有效的翻译列表中
                        boolean isInValidList = false;
                        for (int i = 0; i < textGroupIndices.size(); i++) {
                            if (textGroupIndices.get(i) == groupIndex) {
                                isInValidList = true;
                                break;
                            }
                        }
                        if (!isInValidList) {
                            // 合并组内的文本用于日志输出
                            StringBuilder englishTextForCheck = new StringBuilder();
                            for (CoordinateTextStripper.TextItem item : group) {
                                englishTextForCheck.append(item.text).append(" ");
                            }
                            String englishForCheck = cleanOCRText(englishTextForCheck.toString().trim());
                            if (!englishForCheck.isEmpty() && englishForCheck.length() >= 2) {
                                System.out.println("  [跳过] 文本组 [" + (groupIndex + 1) + "] 已被过滤（无意义文本）: \"" +
                                        englishForCheck.substring(0, Math.min(50, englishForCheck.length())) + "...\"");
                            } else {
                                System.out.println("  [跳过] 文本组 [" + (groupIndex + 1) + "] 已被过滤（无意义文本）");
                            }
                            continue; // 跳过这个文本组
                        }
                    }

                    // 检查是否是多行文本
                    boolean isMultiline = group.size() > 1;

                    // 合并组内的文本
                    StringBuilder englishText = new StringBuilder();
                    float groupX = Float.MAX_VALUE;
                    // 初始化groupY和groupBottomY
                    float groupY;
                    float groupBottomY;
                    if (isReversedCoordinate) {
                        // 反向坐标系：Y值小在上，Y值大在下
                        // groupY应该是最小值（页面顶部），groupBottomY应该是最大值（页面底部）
                        groupY = Float.MAX_VALUE; // 用于Math.min找到最小值（页面顶部）
                        groupBottomY = 0; // 用于Math.max找到最大值（页面底部）
                    } else {
                        // 标准PDFBox坐标系：Y值大在上，Y值小在下
                        // groupY应该是最大值（页面顶部），groupBottomY应该是最小值（页面底部）
                        groupY = 0; // 用于Math.max找到最大值（页面顶部）
                        groupBottomY = Float.MAX_VALUE; // 用于Math.min找到最小值（页面底部）
                    }
                    float groupEndX = 0; // 英文文本的结束X坐标

                    for (int idx = 0; idx < group.size(); idx++) {
                        CoordinateTextStripper.TextItem item = group.get(idx);
                        englishText.append(item.text).append(" ");
                        groupX = Math.min(groupX, item.x);

                        // 根据坐标系方向计算groupY和groupBottomY
                        if (isReversedCoordinate) {
                            // 反向坐标系：Y值小在上，Y值大在下
                            // groupY应该是最小值（页面顶部），groupBottomY应该是最大值（页面底部）
                            groupY = Math.min(groupY, item.y);
                            groupBottomY = Math.max(groupBottomY, item.y);
                        } else {
                            // 标准PDFBox坐标系：Y值大在上，Y值小在下
                            // groupY应该是最大值（页面顶部），groupBottomY应该是最小值（页面底部）
                            groupY = Math.max(groupY, item.y);
                            groupBottomY = Math.min(groupBottomY, item.y);
                        }

                        // 计算文本块的结束位置（文本开始位置 + 文本宽度）
                        float itemEndX = item.x + item.text.length() * 6; // 估算字符宽度
                        groupEndX = Math.max(groupEndX, itemEndX);
                    }


                    String english = englishText.toString().trim();
                    if (english.isEmpty() || english.length() < 2) {
                        System.out.println("⚠️ 文本为空，跳过");
                        continue;
                    }

                    // 清理OCR错误的前缀/后缀（如 "Bx Pps AH" 这样的无意义前缀）
                    english = cleanOCRText(english);
                    if (english.isEmpty() || english.length() < 2) {
                        System.out.println("⚠️ 清理后文本为空，跳过");
                        continue;
                    }

                    // OCR过滤已移除，所有文本都会进行翻译

                    // 检查文本中是否包含"分行符变n"（复制粘贴时换行符变成字母n，导致多行被合并）
                    List<String> corruptedNewlineItems = splitCorruptedNewlineItems(english);
                    if (corruptedNewlineItems.size() > 1) {
                        System.out.println("📋 检测到 " + corruptedNewlineItems.size() + " 个分行项（分行符变n），使用批量翻译结果");
                        // 使用批量翻译结果（textsToTranslate已按拆分后的项存储）
                        for (int itemIdx = 0; itemIdx < corruptedNewlineItems.size(); itemIdx++) {
                            String item = corruptedNewlineItems.get(itemIdx);
                            String translated = textsToTranslateIndex < translatedTexts.size() ?
                                    translatedTexts.get(textsToTranslateIndex) : translateParallel(java.util.Collections.singletonList(item), "en", "zh").get(0);
                            if (textsToTranslateIndex < translatedTexts.size()) textsToTranslateIndex++;
                            if (shouldSkipDrawingFormulaOrSymbolOnly(item, translated, hybridEmbeddedImageOcrPass)) {
                                System.out.println("  [跳过绘制] [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] 公式/符号译文不写入PDF: " + translated);
                                continue;
                            }
                            System.out.println("✅ [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] " + item + " → " + translated);
                            float itemX = calculateItemX(group, english, item, itemIdx, corruptedNewlineItems);
                            float itemY = calculateNumberedItemY(group, itemIdx, pageHeight, isMultiline);
                            drawTranslationSimple(contentStream, chineseFont, itemX, itemY, translated, pageWidth, pageHeight);
                        }
                        continue;
                    } else if (corruptedNewlineItems.size() == 1 && !corruptedNewlineItems.get(0).equals(english)) {
                        // 单行被清理了开头的"n"（如 nOOP Recap -> OOP Recap）
                        english = corruptedNewlineItems.get(0);
                    }

                    // 检查文本中是否包含数字序号列表（如1. 2. 3. 4.）
                    List<String> numberedItems = splitNumberedItems(english);

                    // 如果有多个数字序号项，分别翻译每个（优化：使用并行翻译）
                    if (numberedItems.size() > 1) {
                        System.out.println("🔢 检测到 " + numberedItems.size() + " 个数字序号项，并行翻译");
                        // 如果这个文本在textsToTranslate中，需要跳过对应的翻译结果
                        if (textsToTranslateIndex < textsToTranslate.size() &&
                                textsToTranslate.get(textsToTranslateIndex).equals(english)) {
                            textsToTranslateIndex++;
                        }
                        // 并行翻译所有列表项
                        List<String> translatedItems = translateParallel(numberedItems, "en", "zh");
                        for (int itemIdx = 0; itemIdx < numberedItems.size(); itemIdx++) {
                            String item = numberedItems.get(itemIdx);
                            String translated = translatedItems.get(itemIdx);
                            if (shouldSkipDrawingFormulaOrSymbolOnly(item, translated, hybridEmbeddedImageOcrPass)) {
                                System.out.println("  [跳过绘制] [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] 公式/符号译文不写入PDF: " + translated);
                                continue;
                            }
                            System.out.println("✅ [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] " + item + " → " + translated);

                            // 计算每个列表项的位置，使用准确的X坐标
                            float itemX = calculateItemX(group, english, item, itemIdx, numberedItems);
                            float itemY = calculateNumberedItemY(group, itemIdx, pageHeight, isMultiline);

                            // 绘制这一项的翻译（列表项不需要重叠检测）
                            drawTranslationSimple(contentStream, chineseFont, itemX, itemY, translated, pageWidth, pageHeight);
                        }
                        continue; // 跳过下面的统一处理
                    }

                    // 检查文本中是否包含特殊符号 U+F06C（分段标志）
                    List<String> specialSymbolItems = splitSpecialSymbolItems(english);

                    // 如果有多个特殊符号段落，分别翻译每个（优化：使用并行翻译）
                    if (specialSymbolItems.size() > 1) {
                        System.out.println("🔷 检测到 " + specialSymbolItems.size() + " 个特殊符号段落，并行翻译");
                        // 如果这个文本在textsToTranslate中，需要跳过对应的翻译结果
                        if (textsToTranslateIndex < textsToTranslate.size() &&
                                textsToTranslate.get(textsToTranslateIndex).equals(english)) {
                            textsToTranslateIndex++;
                        }
                        // 并行翻译所有段落
                        List<String> translatedItems = translateParallel(specialSymbolItems, "en", "zh");
                        for (int itemIdx = 0; itemIdx < specialSymbolItems.size(); itemIdx++) {
                            String item = specialSymbolItems.get(itemIdx);
                            String translated = translatedItems.get(itemIdx);
                            if (shouldSkipDrawingFormulaOrSymbolOnly(item, translated, hybridEmbeddedImageOcrPass)) {
                                System.out.println("  [跳过绘制] [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] 公式/符号译文不写入PDF: " + translated);
                                continue;
                            }
                            System.out.println("✅ [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] " + item + " → " + translated);

                            // 计算每个段落的位置，使用准确的X坐标
                            float itemX = calculateItemX(group, english, item, itemIdx, specialSymbolItems);
                            float itemY = calculateSpecialSymbolItemY(group, itemIdx, pageHeight, isMultiline, specialSymbolItems.size(), isReversedCoordinate);

                            // 绘制这一项的翻译（列表项不需要重叠检测）
                            drawTranslationSimple(contentStream, chineseFont, itemX, itemY, translated, pageWidth, pageHeight);
                        }
                        continue; // 跳过下面的统一处理
                    }

                    // 检查是否包含以短横线开头的分行/列表项（–/—/-），视为新段落分别翻译
                    List<String> dashItems = splitDashItems(english);
                    if (dashItems.size() > 1) {
                        System.out.println("🔍 检测到 " + dashItems.size() + " 个短横线分段项（–/—/-），并行翻译");
                        // 如果这个文本在textsToTranslate中，需要跳过对应的翻译结果
                        if (textsToTranslateIndex < textsToTranslate.size() &&
                                textsToTranslate.get(textsToTranslateIndex).equals(english)) {
                            textsToTranslateIndex++;
                        }
                        List<String> translatedItems = translateParallel(dashItems, "en", "zh");
                        for (int itemIdx = 0; itemIdx < dashItems.size(); itemIdx++) {
                            String item = dashItems.get(itemIdx);
                            String translated = translatedItems.get(itemIdx);
                            if (shouldSkipDrawingFormulaOrSymbolOnly(item, translated, hybridEmbeddedImageOcrPass)) {
                                System.out.println("  [跳过绘制] [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] 公式/符号译文不写入PDF: " + translated);
                                continue;
                            }
                            System.out.println("✅ [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] " + item + " → " + translated);

                            float itemX = calculateItemX(group, english, item, itemIdx, dashItems);
                            // 关键：短横线子要点按其自身所在行定位译文 Y（而不是按整个组顶部等距堆叠）
                            float itemY = calculateItemYFromTop(group, english, item, itemIdx, dashItems, pageHeight, isReversedCoordinate);
                            drawTranslationSimple(contentStream, chineseFont, itemX, itemY, translated, pageWidth, pageHeight);
                        }
                        continue;
                    }

                    // 检查文本中是否包含多个"•"（同一行或跨行的列表项）
                    List<String> bulletItems = splitBulletItems(english);

                    // 如果有多个列表项，分别翻译每个（优化：使用并行翻译）
                    if (bulletItems.size() > 1) {
                        System.out.println("🔍 检测到 " + bulletItems.size() + " 个列表项，并行翻译");
                        // 如果这个文本在textsToTranslate中，需要跳过对应的翻译结果
                        if (textsToTranslateIndex < textsToTranslate.size() &&
                                textsToTranslate.get(textsToTranslateIndex).equals(english)) {
                            textsToTranslateIndex++;
                        }
                        // 并行翻译所有列表项
                        List<String> translatedItems = translateParallel(bulletItems, "en", "zh");
                        for (int itemIdx = 0; itemIdx < bulletItems.size(); itemIdx++) {
                            String item = bulletItems.get(itemIdx);
                            String translated = translatedItems.get(itemIdx);
                            if (shouldSkipDrawingFormulaOrSymbolOnly(item, translated, hybridEmbeddedImageOcrPass)) {
                                System.out.println("  [跳过绘制] [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] 公式/符号译文不写入PDF: " + translated);
                                continue;
                            }
                            System.out.println("✅ [" + (groupIndex + 1) + "-" + (itemIdx + 1) + "] " + item + " → " + translated);

                            // 计算每个列表项的位置，使用准确的X坐标
                            float itemX = calculateItemX(group, english, item, itemIdx, bulletItems);
                            float itemY = calculateBulletItemY(group, itemIdx, pageHeight, isMultiline);

                            // 绘制这一项的翻译（列表项不需要重叠检测）
                            drawTranslationSimple(contentStream, chineseFont, itemX, itemY, translated, pageWidth, pageHeight);
                        }
                        continue; // 跳过下面的统一处理
                    }

                    // 翻译文本（单个列表项或非列表项）
                    // 检查当前文本是否在textsToTranslate中，如果是，使用对应的批量翻译结果
                    String translated;
                    if (textsToTranslateIndex < textsToTranslate.size() &&
                            textsToTranslate.get(textsToTranslateIndex).equals(english)) {
                        // 使用批量翻译的结果
                        translated = translatedTexts.get(textsToTranslateIndex);
                        textsToTranslateIndex++;
                        System.out.println("✅ 使用批量翻译结果: " + translated);
                    } else {
                        // 没有对应的批量翻译结果，单独翻译
                        translated = translateWithSmartAPI(english, "en", "zh");
                        System.out.println("🔄 单独翻译: " + translated);
                    }

                    if (shouldSkipDrawingFormulaOrSymbolOnly(english, translated, hybridEmbeddedImageOcrPass)) {
                        System.out.println("  [跳过绘制] 文本组 [" + (groupIndex + 1) + "] 公式/符号/示意图乱码译文不写入PDF");
                        continue;
                    }

                    // 规则1：若译文与原文在规范化后完全一致，且判断为代码段（但非注释），则不在下方绘制译文
                    if (shouldSkipDrawingTranslation(english, translated)) {
                        System.out.println("  [跳过绘制] 文本组 [" + (groupIndex + 1) + "] 判定为代码且译文与原文一致，不添加下方译文");
                        continue;
                    }

                    // 计算翻译位置
                    // X坐标：直接使用groupX（PDFBox坐标系，从左到右递增，原点在左下角）
                    // groupX是文本组的最左端位置，应该与原文对齐
                    float translationX = groupX;

                    // 检查X坐标是否超出页面范围，如果超出则调整
                    float leftMargin = 20.0f;
                    float rightMargin = 20.0f;
                    if (translationX < leftMargin) {
                        translationX = leftMargin;
                    } else if (translationX > pageWidth - rightMargin) {
                        translationX = pageWidth - rightMargin;
                    }

                    float translationY;

                    // 计算译文Y坐标 - 优先放在原文行与行之间的空白处
                    float fontSize = TRANSLATION_ZH_FONT_SIZE_PT;
                    float lineHeight = TRANSLATION_ZH_LINE_HEIGHT_PT; // 行高

                    // 估算译文的总高度（考虑可能的多行）
                    float availableWidth = pageWidth - groupX - 20.0f; // 可用宽度
                    float charWidth = fontSize * 1.1f; // 字符宽度
                    int charsPerLine = Math.max(1, (int) (availableWidth / charWidth));
                    List<String> estimatedLines = wrapText(translated, charsPerLine);
                    float translationHeight = estimatedLines.size() * lineHeight;

                    float minGap = translationHeight + 10.0f; // 行间空白的最小值，需要能容纳译文高度+10像素边距

                    // 计算当前文本组的底部Y坐标（从顶部开始）
                    // 统一处理：无论哪种坐标系，都转换为"从顶部开始"的坐标系统
                    float currentBottomY;
                    if (isMultiline) {
                        // 多行文本：groupBottomY是底部Y坐标（在PDFBox坐标系中）
                        // 需要转换为"从顶部开始"的坐标
                        if (isReversedCoordinate) {
                            // 反向坐标系：groupBottomY是最大值（页面底部），需要转换为从顶部开始
                            currentBottomY = pageHeight - groupBottomY;
                        } else {
                            // 标准坐标系：groupBottomY是最小值（页面底部），需要转换为从顶部开始
                            currentBottomY = pageHeight - groupBottomY;
                        }
                    } else {
                        // 单行文本的底部（估算文本高度）
                        float singleLineHeight = fontSize * 0.8f;
                        if (isReversedCoordinate) {
                            // 反向坐标系：groupY是最小值（页面顶部）
                            float groupTopYFromTop = pageHeight - groupY;
                            currentBottomY = groupTopYFromTop + singleLineHeight;
                        } else {
                            // 标准坐标系：groupY是最大值（页面顶部）
                            float groupTopYFromTop = pageHeight - groupY;
                            currentBottomY = groupTopYFromTop + singleLineHeight;
                        }
                    }

                    // 尝试找到下一个文本组，计算行间空白
                    float nextTopY = -1;
                    if (groupIndex + 1 < textGroups.size()) {
                        List<CoordinateTextStripper.TextItem> nextGroup = textGroups.get(groupIndex + 1);
                        float nextGroupY;
                        if (isReversedCoordinate) {
                            // 反向坐标系：找到最小值（页面顶部）
                            nextGroupY = Float.MAX_VALUE;
                            for (CoordinateTextStripper.TextItem item : nextGroup) {
                                nextGroupY = Math.min(nextGroupY, item.y);
                            }
                        } else {
                            // 标准坐标系：找到最大值（页面顶部）
                            nextGroupY = 0;
                            for (CoordinateTextStripper.TextItem item : nextGroup) {
                                nextGroupY = Math.max(nextGroupY, item.y);
                            }
                        }
                        // 转换为"从顶部开始"的坐标
                        nextTopY = pageHeight - nextGroupY;
                    }

                    // 如果找到下一个文本组，且行间空白足够，将译文放在中间
                    if (nextTopY > 0 && (nextTopY - currentBottomY) >= minGap) {
                        // 计算空白位置的中间
                        float gapCenter = (currentBottomY + nextTopY) / 2;
                        // 将译文放在中间位置
                        translationY = gapCenter - translationHeight / 2;

                        // 确保译文不会超出空白区域
                        float minY = currentBottomY + 5; // 距离当前文本至少5像素
                        float maxY = nextTopY - translationHeight - 5; // 距离下一个文本至少5像素
                        translationY = Math.max(minY, Math.min(maxY, translationY));

                        System.out.println("  [位置计算] 将译文放在行间空白处: 当前底部=" + currentBottomY +
                                ", 下一个顶部=" + nextTopY + ", 空白=" + (nextTopY - currentBottomY) +
                                ", 译文高度=" + translationHeight + ", 译文Y=" + translationY);
                    } else {
                        // 没有下一个文本组或空白不够，放在原文下方
                        // OCR模式下，优先放在原文第一行下方；文本层模式下，放在原文最后一行下方
                        float spacing = isOCRMode ? 12.0f : 8.0f; // OCR模式增加间距，确保不重合

                        if (isOCRMode) {
                            // OCR模式：放在原文第一行下方（避免与原文重合）
                            float englishFirstLineTopY;  // 原文第一行顶部Y（从顶部开始，0=页面顶）
                            float englishLineHeight = fontSize * 1.2f; // OCR文本行高

                            if (isReversedCoordinate) {
                                // 反向坐标系：Y值小在上，groupY 已是“从顶部算”的语义（小=上）
                                englishFirstLineTopY = groupY;
                            } else {
                                // 标准PDFBox坐标系：groupY是最大值（页面顶部），转为从顶算
                                englishFirstLineTopY = pageHeight - groupY;
                            }

                            // 计算原文第一行的底部位置
                            float englishFirstLineBottomY = englishFirstLineTopY + englishLineHeight;
                            translationY = englishFirstLineBottomY + spacing;

                            System.out.println("  [位置计算-OCR] 将译文放在原文第一行下方: 第一行顶部Y=" + englishFirstLineTopY +
                                    ", 第一行底部Y=" + englishFirstLineBottomY + ", 间距=" + spacing +
                                    ", 译文Y=" + translationY);
                        } else {
                            // 文本层模式：放在原文最后一行下方
                            if (isMultiline) {
                                // 多行文本：使用groupBottomY（底部Y坐标）
                                float englishBottomY;
                                if (isReversedCoordinate) {
                                    // 反向坐标系：groupBottomY是最大值（页面底部）
                                    englishBottomY = pageHeight - groupBottomY;
                                } else {
                                    // 标准坐标系：groupBottomY是最小值（页面底部）
                                    englishBottomY = pageHeight - groupBottomY;
                                }
                                translationY = englishBottomY + spacing;
                            } else {
                                // 单行文本：使用groupY（顶部Y坐标）+ 文本高度
                                float englishTopY;
                                float singleLineHeight = fontSize * 0.8f;
                                if (isReversedCoordinate) {
                                    // 反向坐标系：groupY是最小值（页面顶部）
                                    englishTopY = pageHeight - groupY;
                                } else {
                                    // 标准坐标系：groupY是最大值（页面顶部）
                                    englishTopY = pageHeight - groupY;
                                }
                                translationY = englishTopY + singleLineHeight + spacing;
                            }

                            System.out.println("  [位置计算-文本层] 将译文放在原文下方: Y=" + translationY + ", 高度=" + translationHeight);
                        }

                        if (translationY + translationHeight > pageHeight) {
                            translationY = pageHeight - translationHeight - 10;
                        }
                    }

                    // ============================================
                    // 位置处理：根据模式选择不同的处理方式
                    // ============================================
                    if (!isOCRMode) {
                        // ============================================
                        // 文本层模式：应用轴对称处理
                        // ============================================
                        System.out.println("  [模式] 文本层模式 - 应用轴对称处理");
                        float centerLineY = pageHeight / 2.0f; // 页面中心线（对于540高度的页面，这是270）

                        // 计算原文的顶部Y坐标（从顶部开始）
                        float englishTopYFromTop;
                        if (isMultiline) {
                            // 多行文本：使用groupY（顶部Y坐标）
                            if (isReversedCoordinate) {
                                englishTopYFromTop = pageHeight - groupY;
                            } else {
                                englishTopYFromTop = pageHeight - groupY;
                            }
                        } else {
                            // 单行文本：使用groupY（顶部Y坐标）
                            if (isReversedCoordinate) {
                                englishTopYFromTop = pageHeight - groupY;
                            } else {
                                englishTopYFromTop = pageHeight - groupY;
                            }
                        }

                        // 对原文的Y坐标相对于中心线做轴对称处理
                        // 如果原文在Y1位置，译文应该在对称位置：Y2 = 2 * centerLineY - Y1
                        float symmetricY = 2 * centerLineY - englishTopYFromTop;

                        // 译文应该放在对称位置，但要考虑译文高度
                        // 如果原文顶部在Y1，译文顶部应该在对称位置Y2
                        translationY = symmetricY;

                        // 再往下移动8.8像素点
                        float downwardOffset = 8.8f;
                        translationY += downwardOffset;

                        System.out.println("  [轴对称处理] 原文顶部Y=" + englishTopYFromTop + ", 中心线=" + centerLineY +
                                ", 对称后Y=" + symmetricY + ", 下移" + downwardOffset + "像素后Y=" + translationY);

                        // 确保译文不会超出页面范围
                        if (translationY < 0) {
                            translationY = 0;
                        }
                        if (translationY + translationHeight > pageHeight) {
                            translationY = pageHeight - translationHeight - 10;
                        }
                    } else {
                        // ============================================
                        // OCR模式：不使用轴对称处理，使用正常的位置计算
                        // 优化：确保译文放在原文第一行下方，且不重合
                        // ============================================
                        System.out.println("  [模式] OCR模式 - 不使用轴对称处理，使用正常位置计算");

                        // OCR模式下，重新计算译文位置，确保放在原文第一行下方
                        // 计算原文第一行的底部位置（从顶部开始的坐标，0=页面顶）
                        float englishFirstLineTopY;  // 原文第一行顶部Y（从顶部开始）
                        float englishFirstLineBottomY; // 原文第一行底部Y（从顶部开始）

                        // 估算原文第一行的文本高度
                        float englishLineHeight = fontSize * 1.2f; // OCR文本行高，稍微大一点以确保不重合

                        if (isReversedCoordinate) {
                            // 反向坐标系：Y值小在上，groupY 已是“从顶部算”的语义（小=上）
                            englishFirstLineTopY = groupY;
                        } else {
                            // 标准PDFBox坐标系：groupY是最大值（页面顶部），转为从顶算
                            englishFirstLineTopY = pageHeight - groupY;
                        }

                        // 计算原文第一行的底部位置
                        englishFirstLineBottomY = englishFirstLineTopY + englishLineHeight;

                        // 译文应该放在原文第一行下方，增加足够的间距避免重合
                        float ocrSpacing = 12.0f; // OCR模式下增加间距，确保不重合
                        translationY = englishFirstLineBottomY + ocrSpacing;

                        float originalOCR_Y = translationY;

                        System.out.println("  [OCR位置调整] 原文第一行顶部Y=" + englishFirstLineTopY +
                                ", 第一行底部Y=" + englishFirstLineBottomY +
                                ", 间距=" + ocrSpacing +
                                ", 译文Y=" + translationY +
                                ", 译文高度=" + translationHeight);

                        // 确保译文不会超出页面范围
                        if (translationY + translationHeight > pageHeight) {
                            translationY = pageHeight - translationHeight - 10;
                            System.out.println("  [OCR位置调整] 超出页面范围，调整后Y=" + translationY);
                        }

                        // 额外检查：确保译文顶部不会与原文第一行底部重合
                        if (translationY < englishFirstLineBottomY + 5.0f) {
                            translationY = englishFirstLineBottomY + 5.0f;
                            System.out.println("  [OCR位置调整] 防止重合，调整后Y=" + translationY);
                        }
                    }

                    // 检查Y坐标冲突：如果当前译文的Y坐标与已绘制的译文Y坐标相同或非常接近（差异小于2像素），调整X坐标
                    float yConflictThreshold = 2.0f; // Y坐标冲突阈值
                    float adjustedTranslationX = translationX;

                    for (float[] drawn : drawnTranslations) {
                        float drawnY = drawn[0];
                        float drawnEndX = drawn[1];

                        // 检查Y坐标是否冲突（相同或非常接近）
                        if (Math.abs(translationY - drawnY) < yConflictThreshold) {
                            // Y坐标冲突，将X坐标调整到前一句的末尾
                            float spacing = 10.0f; // 两句之间的间距
                            adjustedTranslationX = Math.max(adjustedTranslationX, drawnEndX + spacing);
                            System.out.println("  [Y坐标冲突检测] 检测到Y坐标冲突: 当前Y=" + translationY +
                                    ", 已绘制Y=" + drawnY + ", 已绘制结束X=" + drawnEndX +
                                    ", 调整后X=" + adjustedTranslationX);
                        }
                    }

                    // 计算译文的结束X坐标（用于后续冲突检测）
                    // 估算译文宽度：考虑换行情况
                    // 注意：fontSize、charWidth、rightMargin已在前面定义，这里直接使用
                    // 重新计算availableWidth和charsPerLine，因为X坐标可能已调整
                    float adjustedAvailableWidth = pageWidth - adjustedTranslationX - rightMargin;
                    int adjustedCharsPerLine = (int) (adjustedAvailableWidth / charWidth);

                    // 如果译文会换行，结束X坐标应该是页面宽度减去右边距
                    // 如果不会换行，结束X坐标是起始X + 译文宽度
                    float translationEndX;
                    if (translated.length() > adjustedCharsPerLine && adjustedCharsPerLine > 0) {
                        // 会换行，结束X坐标是页面右边缘
                        translationEndX = pageWidth - rightMargin;
                    } else {
                        // 不会换行，结束X坐标是起始X + 实际宽度
                        translationEndX = adjustedTranslationX + translated.length() * charWidth;
                    }

                    // 将当前译文的位置信息添加到已绘制列表
                    drawnTranslations.add(new float[]{translationY, translationEndX});

                    // 使用调整后的X坐标
                    translationX = adjustedTranslationX;

                    // 添加中文翻译文本（在英文下方）
                    if (TEXTBOX_MODE) {
                        // 文本框模式：创建可编辑的文本框
                        createEditableTextBox(page, translated, translationX, translationY, groupIndex, pageHeight);
                    } else {
                        // 静态文本模式：使用支持自动换行的函数
                        drawTranslation(contentStream, chineseFont, translationX, translationY, translated,
                                pageWidth, pageHeight, textGroups, groupIndex, groupY, groupBottomY,
                                isReversedCoordinate, isOCRMode);
                    }
                }

            } // end else (!isCodePage)

            System.out.println("✅ 页面 " + (pageIndex + 1) + " 完成，共处理 " + textGroups.size() + " 个文本组");
        }
    }

    /**
     * 检测坐标系方向
     * @return true表示反向坐标系（Y值小在上），false表示标准坐标系（Y值大在上）
     * 注意：OCR和文本层都已统一为PDFBox坐标系（Y值大在上），所以通常返回false
     */
    private static boolean detectCoordinateSystem(List<CoordinateTextStripper.TextItem> textItems) {
        if (textItems.isEmpty() || textItems.size() < 2) {
            return false; // 默认标准坐标系（PDFBox坐标系）
        }

        // 按Y值升序排序
        List<CoordinateTextStripper.TextItem> sorted = new ArrayList<>(textItems);
        sorted.sort((a, b) -> Float.compare(a.y, b.y));

        float firstY = sorted.get(0).y;
        float lastY = sorted.get(sorted.size() - 1).y;

        // 在PDFBox坐标系中，Y值大在上，Y值小在下
        // 如果第一个Y值小于最后一个Y值（升序排序后），说明Y值小在上（反向坐标系）
        // 如果第一个Y值大于最后一个Y值，说明Y值大在上（标准PDFBox坐标系）
        // 由于OCR和文本层都已统一为PDFBox坐标系，通常firstY < lastY应该很少出现
        boolean isReversed = (firstY < lastY);

        if (isReversed) {
            System.out.println("  [DEBUG 坐标系检测] 检测到反向坐标系（Y值小在上）");
        } else {
            System.out.println("  [DEBUG 坐标系检测] 检测到标准PDFBox坐标系（Y值大在上）");
        }

        return isReversed;
    }

    /** OCR 合并判断用：略小于默认 6px/字，减轻右侧批注与正文因「框过宽」被误判为 X 重叠 */
    private static float ocrRightEdgeX(CoordinateTextStripper.TextItem item) {
        if (item == null || item.text == null) {
            return item != null ? item.x : 0;
        }
        return item.x + item.text.length() * 5.2f;
    }

    private static float ocrBlockRightEdgeX(List<CoordinateTextStripper.TextItem> blockItems) {
        float m = Float.NEGATIVE_INFINITY;
        for (CoordinateTextStripper.TextItem it : blockItems) {
            m = Math.max(m, ocrRightEdgeX(it));
        }
        return m == Float.NEGATIVE_INFINITY ? 0 : m;
    }

    /**
     * 文本块边界框类，用于存储文本块的边界信息
     */
    private static class TextBlock {
        float minX, maxX, minY, maxY;
        List<CoordinateTextStripper.TextItem> items;

        TextBlock(CoordinateTextStripper.TextItem item) {
            this.minX = item.x;
            this.maxX = item.x + item.text.length() * 6; // 估算宽度
            this.minY = item.y;
            this.maxY = item.y;
            this.items = new ArrayList<>();
            this.items.add(item);
        }

        void addItem(CoordinateTextStripper.TextItem item) {
            items.add(item);
            minX = Math.min(minX, item.x);
            maxX = Math.max(maxX, item.x + item.text.length() * 6);
            minY = Math.min(minY, item.y);
            maxY = Math.max(maxY, item.y);
        }

        boolean canMerge(CoordinateTextStripper.TextItem item, float yThreshold, float xThreshold) {
            return canMerge(item, yThreshold, xThreshold, false, 0, false);
        }

        /**
         * 检查是否可以合并文本项
         * @param item 要合并的文本项
         * @param yThreshold Y坐标阈值
         * @param xThreshold X坐标阈值
         * @param checkWrap 是否检查换行情况（放宽条件）
         * @param pageWidth 页面宽度（>0 时用于左右分栏保护：左半页块不与右半页项合并）
         * @param isOCRMode OCR 模式下用略紧的右边界估算并拒绝「左侧正文 + 右侧批注」误并
         */
        boolean canMerge(CoordinateTextStripper.TextItem item, float yThreshold, float xThreshold, boolean checkWrap, float pageWidth, boolean isOCRMode) {
            // 计算文本项的边界
            float itemMinX = item.x;
            float itemMaxX = item.x + item.text.length() * 6;
            float itemY = item.y;
            float itemRightForMerge = isOCRMode ? ocrRightEdgeX(item) : itemMaxX;
            float blockLeftForMerge = minX;
            float blockRightForMerge = isOCRMode ? ocrBlockRightEdgeX(items) : maxX;

            // 如果检查换行情况，放宽阈值
            float adjustedYThreshold = yThreshold;
            float adjustedXThreshold = xThreshold;
            boolean isWrapCase = false; // 标记是否是换行情况

            if (checkWrap) {
                // 检查是否是换行情况：当前文本块没有以句号等结束，且下一行以小写字母开头
                String lastText = "";
                if (!items.isEmpty()) {
                    lastText = items.get(items.size() - 1).text.trim();
                }
                String nextText = item.text.trim();

                // 检查当前文本块是否以句号、问号、感叹号等结束
                boolean endsWithSentenceEnd = false;
                if (!lastText.isEmpty()) {
                    char lastChar = lastText.charAt(lastText.length() - 1);
                    endsWithSentenceEnd = (lastChar == '.' || lastChar == '!' || lastChar == '?' ||
                            lastChar == ';' || lastChar == ':');
                }

                // 检查下一行是否以小写字母开头（表示是句子的延续）
                // 但要排除"n "或"n+大写/数字"的情况（这是复制粘贴时分行符变成的"n"，不应该合并）
                boolean startsWithLowerCase = false;
                boolean isNSpaceSymbol = false; // 检查是否是分行符变"n"的符号（n 、nOOP、nWhat等）

                if (!nextText.isEmpty()) {
                    // 检查是否是分行符变"n"：n后跟空格、或n后直接跟大写字母/数字（如nOOP、nWhat、nSOLID）
                    if (nextText.startsWith("n ") ||
                            (nextText.length() > 1 && nextText.startsWith("n") &&
                                    (Character.isUpperCase(nextText.charAt(1)) || Character.isDigit(nextText.charAt(1))))) {
                        isNSpaceSymbol = true;
                    } else {
                        char firstChar = nextText.charAt(0);
                        startsWithLowerCase = Character.isLowerCase(firstChar);
                    }
                }

                // 如果是换行情况（当前行未结束，下一行以小写字母开头，且不是"n "分行符号），放宽阈值
                if (!endsWithSentenceEnd && startsWithLowerCase && !isNSpaceSymbol) {
                    // 对于换行情况，使用更宽松但合理的阈值
                    // Y阈值：使用固定值40像素（约2-3行的高度），可以处理"disciplined"和"approach"的情况（Y差异约38像素）
                    adjustedYThreshold = 40.0f;
                    adjustedXThreshold = Math.max(80.0f, xThreshold * 3.0f);
                    isWrapCase = true;
                }
            }

            // 检查Y坐标是否接近
            boolean yClose = (itemY >= minY - adjustedYThreshold && itemY <= maxY + adjustedYThreshold) ||
                    (minY >= itemY - adjustedYThreshold && maxY <= itemY + adjustedYThreshold);

            if (!yClose) {
                return false;
            }

            // OCR：右侧批注/强调（与左侧正文之间有明显空白）不要并入左侧块，减轻「Tight coupling!」类旁注混进句子
            if (pageWidth > 0 && isOCRMode && !checkWrap) {
                float bodyRightLimit = pageWidth * 0.48f;
                float annoLeftLimit = pageWidth * 0.54f;
                if (itemMinX >= annoLeftLimit && blockRightForMerge < bodyRightLimit) {
                    float gapRight = itemMinX - blockRightForMerge;
                    if (gapRight > 28f) {
                        return false;
                    }
                }
            }

            // 如果是换行情况，需要额外检查Y坐标差异和X坐标
            if (isWrapCase) {
                // 额外检查：确保Y坐标差异不超过45像素（防止过度合并）
                float yDiff = Math.abs(itemY - (minY + maxY) / 2);
                if (yDiff > 45.0f) {
                    return false; // Y坐标差异太大，不允许合并
                }
                // 对于换行情况，检查X坐标：
                // 1. 如果X坐标重叠，允许合并
                // 2. 如果下一行在页面左侧（X坐标较小），可能是换行，允许合并
                // 3. 如果X坐标差异太大，可能是不同列的内容，不允许合并
                boolean xOverlap = (itemRightForMerge >= blockLeftForMerge && itemMinX <= blockRightForMerge);

                if (xOverlap) {
                    // X坐标重叠，允许合并
                    return true;
                }

                // 检查X坐标差异
                float xGap = 0;
                if (itemMinX > blockRightForMerge) {
                    xGap = itemMinX - blockRightForMerge;
                } else if (itemRightForMerge < blockLeftForMerge) {
                    xGap = blockLeftForMerge - itemRightForMerge;
                }

                // 对于换行情况，如果下一行在左侧（X坐标较小），且X间距在合理范围内，允许合并
                // 这表示上一行在右侧结束，下一行从左侧开始（典型的换行情况）
                if (itemMinX < blockLeftForMerge && xGap < adjustedXThreshold) {
                    return true;
                }

                // 如果X间距太大，可能是不同列的内容，不允许合并
                return false;
            }

            // 同一行内延续：Y 几乎相同，下一段以小写开头（如 "implementation" 后接 "details of their parent"）
            // 课件上两词之间是正常词距，但 PDF 文本层常对同一行的不同片段给出错误/不一致的 X 坐标，
            // 导致算出的 X 间距很大；此时应主要依据「同 Y + 小写延续」视为同一句并合并
            float sameLineYThreshold = 5.0f;
            boolean sameLineY = (Math.abs(itemY - minY) <= sameLineYThreshold || Math.abs(itemY - maxY) <= sameLineYThreshold);
            if (sameLineY && itemMinX > blockRightForMerge) {
                // 左右分栏保护：一页左半边 1,2,3 段、右半边 4,5,6 段且与 1,2,3 同 Y 时，不应把左段与右段合并
                if (pageWidth > 0 && blockRightForMerge < pageWidth / 2 && itemMinX >= pageWidth / 2) {
                    return false;
                }
                float xGapRight = itemMinX - blockRightForMerge;
                String nextText = item.text.trim();
                boolean nextStartsWithLower = false;
                if (!nextText.isEmpty()) {
                    char c = nextText.charAt(0);
                    if (Character.isLowerCase(c)) {
                        if (nextText.startsWith("n") && nextText.length() > 1
                                && (Character.isUpperCase(nextText.charAt(1)) || Character.isDigit(nextText.charAt(1))))
                            nextStartsWithLower = false;
                        else
                            nextStartsWithLower = true;
                    }
                }
                if (nextStartsWithLower && xGapRight < 150.0f) {
                    return true;
                }
            }

            // 检查X坐标是否重叠或接近（OCR 下用略紧的右边界，减轻误重叠）
            boolean xOverlap = (itemRightForMerge >= blockLeftForMerge && itemMinX <= blockRightForMerge);

            if (xOverlap) {
                // 如果X范围重叠，可以合并（这是同一行或同一列的文本）
                return true;
            }

            // 如果不重叠，检查间距
            float xGap = 0;
            if (itemMinX > blockRightForMerge) {
                xGap = itemMinX - blockRightForMerge;
            } else if (itemRightForMerge < blockLeftForMerge) {
                xGap = blockLeftForMerge - itemRightForMerge;
            }

            // 只有当间距小于阈值时才合并（这表示是同一行的连续文本）
            return xGap < adjustedXThreshold;
        }

        float getCenterY() {
            return (minY + maxY) / 2;
        }

        float getCenterX() {
            return (minX + maxX) / 2;
        }
    }

    /**
     * 使用基于密度的智能分组算法
     * 考虑文本的视觉布局和空间关系
     * @param isOCRMode 是否使用OCR模式（影响排序逻辑）
     * @param pageWidth 页面宽度（>0 时用于左右分栏保护，避免左栏与右栏同 Y 时被合并）
     */
    private static List<List<CoordinateTextStripper.TextItem>> smartGroupTextItems(List<CoordinateTextStripper.TextItem> textItems, boolean isReversedCoordinate, boolean isOCRMode, float pageWidth) {
        if (textItems.isEmpty()) {
            return new ArrayList<>();
        }

        // 计算文本项的平均字符宽度和行高
        float avgCharWidth = 0;
        float avgLineHeight = 0;
        for (CoordinateTextStripper.TextItem item : textItems) {
            if (item.text.length() > 0) {
                avgCharWidth += item.text.length() * 6.0f / item.text.length();
            }
        }
        if (textItems.size() > 0) {
            avgCharWidth /= textItems.size();
        }

        // 计算Y坐标的差异分布，用于确定行高阈值
        List<Float> yCoords = new ArrayList<>();
        for (CoordinateTextStripper.TextItem item : textItems) {
            yCoords.add(item.y);
        }
        Collections.sort(yCoords);

        // 计算相邻Y坐标的差异，找出典型的行间距
        List<Float> yDiffs = new ArrayList<>();
        for (int i = 1; i < yCoords.size(); i++) {
            float diff = Math.abs(yCoords.get(i) - yCoords.get(i - 1));
            if (diff > 1 && diff < 50) { // 过滤掉异常值
                yDiffs.add(diff);
            }
        }

        // 计算中位数作为行高阈值
        float yThreshold = 10.0f; // 默认值，更小的阈值
        if (!yDiffs.isEmpty()) {
            Collections.sort(yDiffs);
            int mid = yDiffs.size() / 2;
            float medianDiff = yDiffs.get(mid);
            // 使用中位数的1.2倍作为阈值，更严格
            yThreshold = Math.max(8.0f, Math.min(15.0f, medianDiff * 1.2f));
        }

        // X坐标差异阈值：基于平均字符宽度，但使用更小的倍数
        // 如果X坐标相差超过这个阈值，认为是不同的文本块
        float xThreshold = Math.max(25.0f, avgCharWidth * 5); // 5个字符的宽度，更敏感

        System.out.println("  [DEBUG 智能分组] Y阈值=" + yThreshold + ", X阈值=" + xThreshold);

        // 创建文本块列表
        List<TextBlock> blocks = new ArrayList<>();

        // 按Y坐标排序（从上到下）
        // OCR模式和文本层模式的坐标系统可能不同，需要分别处理
        List<CoordinateTextStripper.TextItem> sortedItems = new ArrayList<>(textItems);
        sortedItems.sort((a, b) -> {
            int yCompare;
            // OCR模式：通常坐标已经转换为PDFBox坐标系，但可能需要特殊处理
            // 文本层模式：使用PDFBox坐标系
            if (isOCRMode) {
                // OCR模式：根据检测到的坐标系方向排序
                // 如果检测到反向坐标系，按Y升序（小的在前，即顶部在前）
                // 如果检测到标准坐标系，按Y降序（大的在前，即顶部在前）
                if (isReversedCoordinate) {
                    yCompare = Float.compare(a.y, b.y);
                } else {
                    yCompare = Float.compare(b.y, a.y);
                }
            } else {
                // 文本层模式：根据检测到的坐标系方向排序
                if (isReversedCoordinate) {
                    // 反向坐标系：Y值小在上，所以按Y升序排序（小的在前，即顶部在前）
                    yCompare = Float.compare(a.y, b.y);
                } else {
                    // 标准坐标系：Y值大在上，所以按Y降序排序（大的在前，即顶部在前）
                    yCompare = Float.compare(b.y, a.y);
                }
            }
            if (yCompare != 0) return yCompare;
            return Float.compare(a.x, b.x); // Y相同时按X排序
        });

        // 为每个文本项分配或创建文本块
        for (CoordinateTextStripper.TextItem item : sortedItems) {
            TextBlock bestBlock = null;
            float bestScore = Float.MAX_VALUE;

            // 找到最合适的文本块进行合并
            // 优先选择Y坐标最接近且X坐标重叠或接近的文本块
            for (TextBlock block : blocks) {
                // 先尝试普通合并
                if (block.canMerge(item, yThreshold, xThreshold, false, pageWidth, isOCRMode)) {
                    // 计算匹配分数：Y坐标差异越小，分数越好
                    float yDiff = Math.min(Math.abs(item.y - block.minY), Math.abs(item.y - block.maxY));
                    float score = yDiff;

                    // 如果X坐标重叠，优先考虑
                    float itemMinX = item.x;
                    float itemRight = isOCRMode ? ocrRightEdgeX(item) : (item.x + item.text.length() * 6);
                    float blockLeft = block.minX;
                    float blockRight = isOCRMode ? ocrBlockRightEdgeX(block.items) : block.maxX;
                    boolean xOverlap = (itemRight >= blockLeft && itemMinX <= blockRight);
                    if (xOverlap) {
                        score *= 0.5f; // X重叠时分数更好
                    }

                    if (score < bestScore) {
                        bestScore = score;
                        bestBlock = block;
                    }
                } else {
                    // 如果普通合并失败，尝试换行检测（放宽条件）
                    if (block.canMerge(item, yThreshold, xThreshold, true, pageWidth, isOCRMode)) {
                        // 计算匹配分数：Y坐标差异越小，分数越好
                        float yDiff = Math.min(Math.abs(item.y - block.minY), Math.abs(item.y - block.maxY));
                        float score = yDiff * 1.5f; // 换行情况的分数稍差，优先级较低

                        float itemMinX = item.x;
                        float itemRight = isOCRMode ? ocrRightEdgeX(item) : (item.x + item.text.length() * 6);
                        float blockLeft = block.minX;
                        float blockRight = isOCRMode ? ocrBlockRightEdgeX(block.items) : block.maxX;
                        boolean xOverlap = (itemRight >= blockLeft && itemMinX <= blockRight);
                        if (xOverlap) {
                            score *= 0.5f; // X重叠时分数更好
                        }

                        if (score < bestScore) {
                            bestScore = score;
                            bestBlock = block;
                        }
                    }
                }
            }

            // 如果找到合适的文本块，合并；否则创建新的文本块
            if (bestBlock != null) {
                bestBlock.addItem(item);
            } else {
                blocks.add(new TextBlock(item));
            }
        }

        // 将文本块转换为文本组列表
        List<List<CoordinateTextStripper.TextItem>> groups = new ArrayList<>();
        for (TextBlock block : blocks) {
            // 对每个块内的文本项先按Y坐标排序，然后按X坐标排序
            // 这样可以确保换行的情况顺序正确
            block.items.sort((a, b) -> {
                int yCompare = Float.compare(a.y, b.y);
                if (yCompare != 0) return yCompare;
                return Float.compare(a.x, b.x); // Y相同时按X排序
            });
            groups.add(block.items);

            // 调试输出
            StringBuilder groupText = new StringBuilder();
            for (CoordinateTextStripper.TextItem it : block.items) {
                groupText.append(it.text).append(" ");
            }
            System.out.println("  [DEBUG 智能分组] Y=" + block.getCenterY() +
                    ", X范围=[" + block.minX + "-" + block.maxX +
                    "] -> \"" + groupText.toString().trim() + "\"");
        }

        return groups;
    }

    /**
     * 根据X坐标差异拆分文本组
     * 如果同一行内的文本项X坐标相差很大，应该分成不同的组
     * @param minInterItemGapPx 相邻片段之间间隙超过该值则拆组（OCR 可用略大阈值分离旁注）
     */
    private static List<List<CoordinateTextStripper.TextItem>> splitGroupByXGap(List<CoordinateTextStripper.TextItem> group, float minInterItemGapPx) {
        List<List<CoordinateTextStripper.TextItem>> splitGroups = new ArrayList<>();

        if (group.isEmpty()) {
            return splitGroups;
        }

        // 如果只有一个文本项，直接返回
        if (group.size() == 1) {
            splitGroups.add(group);
            return splitGroups;
        }

        // 按X坐标排序
        List<CoordinateTextStripper.TextItem> sortedGroup = new ArrayList<>(group);
        sortedGroup.sort((a, b) -> Float.compare(a.x, b.x));

        // 检查相邻文本项之间的X坐标差异
        List<CoordinateTextStripper.TextItem> currentSubGroup = new ArrayList<>();
        currentSubGroup.add(sortedGroup.get(0));

        for (int i = 1; i < sortedGroup.size(); i++) {
            CoordinateTextStripper.TextItem prevItem = sortedGroup.get(i - 1);
            CoordinateTextStripper.TextItem currentItem = sortedGroup.get(i);

            // 计算前一个文本项的结束X坐标（估算）
            float prevEndX = prevItem.x + prevItem.text.length() * 6; // 估算字符宽度
            float currentStartX = currentItem.x;

            float xGap = currentStartX - prevEndX;
            if (xGap > minInterItemGapPx) {
                // 开始新的子组
                splitGroups.add(new ArrayList<>(currentSubGroup));
                currentSubGroup.clear();
            }
            currentSubGroup.add(currentItem);
        }

        // 添加最后一个子组
        if (!currentSubGroup.isEmpty()) {
            splitGroups.add(currentSubGroup);
        }

        return splitGroups;
    }

    /**
     * 智能分组文本项 - 识别多行文本并合并
     * @param isOCRMode 是否使用OCR模式（影响排序逻辑）
     * @param pageWidth 页面宽度（用于左右分栏保护）
     * @param skipMultilineSentenceMerge 为 true 时不把相邻 OCR 行合并为「同一句话」（混合页嵌入图多行要点）
     */
    private static List<List<CoordinateTextStripper.TextItem>> groupTextByYCoordinate(
            List<CoordinateTextStripper.TextItem> textItems, boolean isReversedCoordinate, boolean isOCRMode,
            float pageWidth, boolean skipMultilineSentenceMerge) {
        List<List<CoordinateTextStripper.TextItem>> groups = new ArrayList<>();

        if (textItems.isEmpty()) {
            return groups;
        }

        // 使用新的智能分组算法进行初步分组
        // 这个算法会考虑文本的视觉布局和空间关系，更准确地识别独立的文本块
        List<List<CoordinateTextStripper.TextItem>> initialGroups = smartGroupTextItems(textItems, isReversedCoordinate, isOCRMode, pageWidth);

        // OCR：同一「行带」内若片段 X 间隙过大（常见：正文 + 右侧批注被误并），拆成多组以便单独翻译/排版
        if (isOCRMode) {
            float ocrSplitGap = pageWidth > 0 ? Math.max(60f, pageWidth * 0.065f) : 60f;
            List<List<CoordinateTextStripper.TextItem>> splitInitial = new ArrayList<>();
            for (List<CoordinateTextStripper.TextItem> g : initialGroups) {
                splitInitial.addAll(splitGroupByXGap(g, ocrSplitGap));
            }
            initialGroups = splitInitial;
        }

        // 先检测并合并多行文本
        List<List<CoordinateTextStripper.TextItem>> multilineGroups = new ArrayList<>();
        for (int i = 0; i < initialGroups.size(); i++) {
            List<CoordinateTextStripper.TextItem> currentLineGroup = initialGroups.get(i);

            // 调试输出：显示当前组
            StringBuilder debugText = new StringBuilder();
            for (CoordinateTextStripper.TextItem item : currentLineGroup) {
                debugText.append(item.text).append(" ");
            }
            System.out.println("  [DEBUG] initialGroups[" + i + "] = \"" + debugText.toString().trim() + "\"");

            // 检查当前行组是否是多行文本的一部分
            MergedGroupResult result = detectAndMergeMultilineText(initialGroups, i, skipMultilineSentenceMerge);
            List<CoordinateTextStripper.TextItem> multilineGroup = result.mergedGroup;
            int mergedCount = result.mergedCount;

            if (mergedCount > 1) {
                // 这是一个多行文本组
                // 输出合并后的完整内容
                StringBuilder mergedText = new StringBuilder();
                for (CoordinateTextStripper.TextItem it : multilineGroup) {
                    mergedText.append(it.text).append(" ");
                }
                System.out.println("  [DEBUG] 合并后的完整内容 = \"" + mergedText.toString().trim() + "\"");

                multilineGroups.add(multilineGroup);
                // 跳过已经被合并的行
                int skipped = 0;
                for (int k = i + 1; k < initialGroups.size() && k < i + mergedCount; k++) {
                    StringBuilder sb = new StringBuilder();
                    for (CoordinateTextStripper.TextItem it : initialGroups.get(k)) {
                        sb.append(it.text).append(" ");
                    }
                    System.out.println("  [DEBUG] 跳过initialGroups[" + k + "] = \"" + sb.toString().trim() + "\"");
                    skipped++;
                }
                System.out.println("  [DEBUG] 总共跳过了" + skipped + "个组");
                i += mergedCount - 1;
            } else {
                // 这是单行文本组
                multilineGroups.add(currentLineGroup);
            }
        }

        // 合并列表项（以"•"开头的连续内容）；混合嵌入图 OCR 跳过，避免把多行要点并成一段
        List<List<CoordinateTextStripper.TextItem>> finalGroups = skipMultilineSentenceMerge
                ? new ArrayList<>(multilineGroups)
                : mergeListItems(multilineGroups);

        // 检查并修正顺序：确保从上到下处理
        // OCR模式和文本层模式的坐标系统可能不同，需要分别处理
        if (!finalGroups.isEmpty() && finalGroups.size() > 1) {
            // 计算每个组的"页面顶部Y坐标"（用于比较）
            List<Float> groupTopYs = new ArrayList<>();
            for (List<CoordinateTextStripper.TextItem> group : finalGroups) {
                float groupTopY;
                if (isReversedCoordinate) {
                    // 反向坐标系：Y值小在上，所以用最小值
                    groupTopY = Float.MAX_VALUE;
                    for (CoordinateTextStripper.TextItem item : group) {
                        groupTopY = Math.min(groupTopY, item.y);
                    }
                } else {
                    // 标准坐标系：Y值大在上，所以用最大值
                    groupTopY = Float.NEGATIVE_INFINITY;
                    for (CoordinateTextStripper.TextItem item : group) {
                        groupTopY = Math.max(groupTopY, item.y);
                    }
                }
                groupTopYs.add(groupTopY);
            }

            float firstGroupTopY = groupTopYs.get(0);
            float lastGroupTopY = groupTopYs.get(groupTopYs.size() - 1);
            System.out.println("  [DEBUG 顺序检查] 第一个组顶部Y=" + firstGroupTopY + ", 最后一个组顶部Y=" + lastGroupTopY +
                    " (OCR模式=" + isOCRMode + ", 反向坐标系=" + isReversedCoordinate + ")");

            // 判断顺序：
            // OCR模式和文本层模式的处理逻辑可能不同
            boolean needReverse = false;

            if (isOCRMode) {
                // OCR模式：根据检测到的坐标系方向来判断
                if (isReversedCoordinate) {
                    // OCR + 反向坐标系：Y值小在上，所以第一个组的Y应该小于最后一个组的Y（顺序正确）
                    // 如果第一个组Y > 最后一个组Y，说明顺序反了
                    if (firstGroupTopY > lastGroupTopY) {
                        needReverse = true;
                    }
                } else {
                    // OCR + 标准坐标系：Y值大在上，所以第一个组的Y应该大于最后一个组的Y（顺序正确）
                    // 如果第一个组Y < 最后一个组Y，说明顺序反了
                    if (firstGroupTopY < lastGroupTopY) {
                        needReverse = true;
                    }
                }
            } else {
                // 文本层模式：根据检测到的坐标系方向来判断
                if (isReversedCoordinate) {
                    // 文本层 + 反向坐标系：Y值小在上，所以第一个组的Y应该小于最后一个组的Y（顺序正确）
                    // 如果第一个组Y > 最后一个组Y，说明顺序反了
                    if (firstGroupTopY > lastGroupTopY) {
                        needReverse = true;
                    }
                } else {
                    // 文本层 + 标准坐标系：Y值大在上，所以第一个组的Y应该大于最后一个组的Y（顺序正确）
                    // 如果第一个组Y < 最后一个组Y，说明顺序反了
                    if (firstGroupTopY < lastGroupTopY) {
                        needReverse = true;
                    }
                }
            }

            if (needReverse) {
                System.out.println("  [DEBUG] 检测到顺序反转，正在修正...");
                java.util.Collections.reverse(finalGroups);
                System.out.println("  [DEBUG] 顺序已修正");
            } else {
                System.out.println("  [DEBUG] 顺序正确（从上到下）");
            }
        }

        return finalGroups;
    }

    /**
     * 检测并合并多行文本
     * 返回合并后的组和实际合并的initialGroups数量
     */
    private static class MergedGroupResult {
        List<CoordinateTextStripper.TextItem> mergedGroup;
        int mergedCount;

        MergedGroupResult(List<CoordinateTextStripper.TextItem> mergedGroup, int mergedCount) {
            this.mergedGroup = mergedGroup;
            this.mergedCount = mergedCount;
        }
    }

    private static MergedGroupResult detectAndMergeMultilineText(
            List<List<CoordinateTextStripper.TextItem>> initialGroups, int startIndex,
            boolean skipMultilineSentenceMerge) {

        List<CoordinateTextStripper.TextItem> currentLineGroup = initialGroups.get(startIndex);
        if (skipMultilineSentenceMerge) {
            return new MergedGroupResult(new ArrayList<>(currentLineGroup), 1);
        }

        List<CoordinateTextStripper.TextItem> mergedGroup = new ArrayList<>();

        // 添加当前行
        mergedGroup.addAll(currentLineGroup);
        int mergedCount = 1; // 记录合并了多少个initialGroups

        // 收集所有文本项用于计算动态阈值
        List<CoordinateTextStripper.TextItem> allTextItems = new ArrayList<>();
        for (List<CoordinateTextStripper.TextItem> group : initialGroups) {
            allTextItems.addAll(group);
        }

        // 检查后续行是否属于同一句话
        for (int i = startIndex + 1; i < initialGroups.size(); i++) {
            List<CoordinateTextStripper.TextItem> nextLineGroup = initialGroups.get(i);

            // 获取当前行和下一行的文本
            StringBuilder currentText = new StringBuilder();
            for (CoordinateTextStripper.TextItem item : currentLineGroup) {
                currentText.append(item.text).append(" ");
            }
            String currentLineText = currentText.toString().trim();

            // 获取合并组的完整文本（用于判断句子是否结束）
            String mergedGroupLastLine = "";
            if (!mergedGroup.isEmpty()) {
                StringBuilder fullText = new StringBuilder();
                for (CoordinateTextStripper.TextItem item : mergedGroup) {
                    fullText.append(item.text).append(" ");
                }
                mergedGroupLastLine = fullText.toString().trim();
            }

            StringBuilder nextText = new StringBuilder();
            for (CoordinateTextStripper.TextItem item : nextLineGroup) {
                nextText.append(item.text).append(" ");
            }
            String nextLineText = nextText.toString().trim();

            // 仅当「下一行」以项目符号开头时停止合并；当前行可以是 ➢/• 要点且下一行为续行（同一条要点）
            if (nextLineText.startsWith("•")) {
                break;
            }

            // 下一行以 ❑、➢、► 等开头 = 新一条要点，不得并入上一组（如 ❑ FSMs… 后接 ➢ States…）
            if (lineStartsWithSlideListMarker(nextLineText)) {
                System.out.println("  [DEBUG] 下一行以幻灯片列表符号开头（➢/❑/►等），停止合并");
                break;
            }

            // FSM/集合枚举行（如 ➢ States = {state 1, ...}），首字符可能是数学体字母而非 ➢，仍须独立成组
            if (lineLooksLikeStateSetOrBraceEnumeration(nextLineText)) {
                System.out.println("  [DEBUG] 下一行疑似状态集/花括号枚举行，停止合并");
                break;
            }

            // 下一行以数字序号开头：新列表项
            if (isNumberedItem(nextLineText)) {
                break;
            }

            // 幻灯片/定义要点：下一行以「标识符 + is/are」开头（如 States is、Outputs is、Inputs is、initialState is）应独立成行
            if (nextLineText.matches("(?i)^[A-Za-z][A-Za-z0-9]{0,20}\\s+is\\s+.*") ||
                    nextLineText.matches("(?i)^[A-Za-z][A-Za-z0-9]{0,20}\\s+are\\s+.*")) {
                System.out.println("  [DEBUG] 下一行为定义要点行（X is/are ...），停止合并");
                break;
            }
            // OCR 常把 "is" 识别成 "1s" / "18" 等：下一行若像「标识符 + 数字 + 小写...」则视为新要点行
            if (nextLineText.matches("(?i)^[a-z][a-z0-9]{1,20}\\s+\\d{1,2}\\s+[a-z].*")) {
                System.out.println("  [DEBUG] 下一行疑似要点行（OCR 误识 is 为数字），停止合并");
                break;
            }

            // 检查：如果合并组的文本以句号结尾，且下一行以大写字母开头，不应该合并
            String textToCheck = !mergedGroupLastLine.isEmpty() ? mergedGroupLastLine : currentLineText;
            char lastChar = textToCheck.isEmpty() ? ' ' : textToCheck.charAt(textToCheck.length() - 1);
            char nextFirstChar = nextLineText.isEmpty() ? ' ' : nextLineText.charAt(0);

            // 检查合并组中是否包含完整的句子（以句号结尾）
            boolean containsCompleteSentence = textToCheck.matches(".*[.!?]\\s*$");

            // 如果包含完整句子，且下一行以大写字母开头，说明是新句子，停止合并
            if (containsCompleteSentence && Character.isUpperCase(nextFirstChar)) {
                System.out.println("  [DEBUG] 检测到完整句子结束(\"" + textToCheck + "\") + 新句子开始(\"" + nextLineText + "\")，停止合并");
                break;
            }

            // 检查通过后，调用isContinuationOfSentence进行更详细的判断
            if (isContinuationOfSentence(currentLineGroup, nextLineGroup, allTextItems)) {
                // 这是同一句话的延续
                String beforeMerge = mergedGroupLastLine;
                mergedGroup.addAll(nextLineGroup);
                currentLineGroup = nextLineGroup; // 更新当前行组用于下次比较
                mergedCount++; // 增加合并计数

                // 更新合并组的完整文本（用于下次检查）
                StringBuilder updatedMergedText = new StringBuilder();
                for (CoordinateTextStripper.TextItem item : mergedGroup) {
                    updatedMergedText.append(item.text).append(" ");
                }
                mergedGroupLastLine = updatedMergedText.toString().trim();

                // 输出合并信息
                System.out.println("  [文本合并] 检测到同一句话被分成多行，已合并:");
                System.out.println("    行1: \"" + (beforeMerge.isEmpty() ? currentLineText : beforeMerge) + "\"");
                System.out.println("    行2: \"" + nextLineText + "\"");
                System.out.println("    合并后: \"" + mergedGroupLastLine + "\"");

                // 检查合并后是否达到完整句子+新句子开始的情况
                // 只有当前文本以句号、问号或感叹号结尾，且下一行以大写字母开头时，才考虑回退
                boolean endsWithPeriod = mergedGroupLastLine.matches(".*[.!?]\\s*$");
                System.out.println("  [DEBUG 合并检查] mergedGroupLastLine=\"" + mergedGroupLastLine + "\", endsWithPeriod=" + endsWithPeriod);

                if (endsWithPeriod && i + 1 < initialGroups.size()) {
                    List<CoordinateTextStripper.TextItem> nextNextGroup = initialGroups.get(i + 1);
                    StringBuilder nextNextText = new StringBuilder();
                    for (CoordinateTextStripper.TextItem item : nextNextGroup) {
                        nextNextText.append(item.text).append(" ");
                    }
                    String nextNextLineText = nextNextText.toString().trim();
                    boolean nextStartsWithUpperCase = !nextNextLineText.isEmpty() && Character.isUpperCase(nextNextLineText.charAt(0));
                    System.out.println("  [DEBUG 合并检查] nextNextLineText=\"" + nextNextLineText + "\", nextStartsWithUpperCase=" + nextStartsWithUpperCase);

                    // 检查下一行是否是新的定义标题（如"Interface design："）
                    boolean isNewDefinition = nextNextLineText.contains(":") || nextNextLineText.contains("：");

                    if (nextStartsWithUpperCase && isNewDefinition) {
                        System.out.println("  [DEBUG] 检测到新定义标题，停止合并");
                        // 不合并下一行，但继续处理当前组
                        break;
                    }
                }
            } else {
                // 不是同一句话，停止合并
                break;
            }
        }

        return new MergedGroupResult(mergedGroup, mergedCount);
    }

    /**
     * 是否以幻灯片列表/要点符号开头（trim 后），用于禁止跨要点合并多行
     */
    private static boolean lineStartsWithSlideListMarker(String line) {
        if (line == null) return false;
        String s = line.replaceFirst("^\uFEFF", "").trim();
        if (s.isEmpty()) return false;
        int idx = indexOfFirstSignificantCodePoint(s);
        if (idx < 0) return false;
        int cp = s.codePointAt(idx);
        // 文本行首的短横线列表（常见：– where ... / — which ... / − which ... / - which ...）
        // 仅当短横线后面紧跟空白时才视为列表符，避免把负号/减号误判为列表项
        if ((cp == 0x2013 || cp == 0x2014 || cp == 0x2212 || cp == '-') && idx + Character.charCount(cp) < s.length()) {
            int nextIdx = idx + Character.charCount(cp);
            int nextCp = s.codePointAt(nextIdx);
            if (Character.isWhitespace(nextCp)) {
                return true;
            }
        }
        // 与首字符对齐比较（避免 ZWSP/BOM/空格后才是 ➢）
        if (s.startsWith("➢", idx) || s.startsWith("►", idx) || s.startsWith("▶", idx) || s.startsWith("▸", idx)
                || s.startsWith("➤", idx) || s.startsWith("❑", idx) || s.startsWith("◆", idx)
                || s.startsWith("◇", idx) || s.startsWith("■", idx)) {
            return true;
        }
        if (cp == 0x2022 || cp == 0x25CF || cp == 0x25AA || cp == 0x25B6 || cp == 0x27A2 || cp == 0x2751) {
            return true;
        }
        // PowerPoint/Keynote 常用箭头区（与源码字面量不一致的 ➢ 变体）
        if (cp >= 0x2794 && cp <= 0x27BF) {
            return true;
        }
        if (cp >= 0x25B6 && cp <= 0x25BF) {
            return true;
        }
        if (cp == 0x276F) {
            return true;
        }
        return false;
    }

    /** 跳过 BOM、零宽字符与空白，返回首个「可见」字符下标 */
    private static int indexOfFirstSignificantCodePoint(String s) {
        int i = 0;
        while (i < s.length()) {
            int cp = s.codePointAt(i);
            if (cp != 0xFEFF && cp != 0x200B && cp != 0x2060 && !Character.isWhitespace(cp)) {
                return i;
            }
            i += Character.charCount(cp);
        }
        return -1;
    }

    /**
     * 下一行是否为「States = { state 1, ... }」类枚举（首词可能是数学斜体 States，未必以 ➢ 开头）
     */
    private static boolean lineLooksLikeStateSetOrBraceEnumeration(String line) {
        if (line == null) return false;
        String t = line.replaceAll("\\s+", " ").trim();
        if (t.length() < 12) return false;
        int o = t.indexOf('{');
        int c = t.indexOf('}');
        if (o < 0 || c <= o || !t.contains("=")) {
            return false;
        }
        String inner = t.substring(o + 1, c).toLowerCase(Locale.ROOT);
        return inner.contains("state");
    }

    /**
     * 合并列表项（以"•"开头的连续内容）
     */
    private static List<List<CoordinateTextStripper.TextItem>> mergeListItems(
            List<List<CoordinateTextStripper.TextItem>> groups) {

        List<List<CoordinateTextStripper.TextItem>> mergedGroups = new ArrayList<>();

        for (int i = 0; i < groups.size(); i++) {
            List<CoordinateTextStripper.TextItem> currentGroup = groups.get(i);

            // 获取当前组的文本
            StringBuilder groupText = new StringBuilder();
            for (CoordinateTextStripper.TextItem item : currentGroup) {
                groupText.append(item.text).append(" ");
            }
            String text = groupText.toString().trim();

            // 检查是否以"•"开头
            if (text.startsWith("•")) {
                // 这是一个列表项，合并后续内容直到下一个"•"或新标题
                List<CoordinateTextStripper.TextItem> mergedListGroup = new ArrayList<>(currentGroup);
                int mergedCount = 0; // 记录合并了多少个后续组

                // 继续查找后续内容
                for (int j = i + 1; j < groups.size(); j++) {
                    List<CoordinateTextStripper.TextItem> nextGroup = groups.get(j);

                    // 获取下一组的文本
                    StringBuilder nextText = new StringBuilder();
                    for (CoordinateTextStripper.TextItem item : nextGroup) {
                        nextText.append(item.text).append(" ");
                    }
                    String nextTextStr = nextText.toString().trim();

                    // 下一组以其它列表符号开头（如 ➢/❑/►/■/– 等），视为新条目，停止合并
                    if (lineStartsWithSlideListMarker(nextTextStr)) {
                        break;
                    }

                    // 如果下一组也以"•"开头，停止合并
                    if (nextTextStr.startsWith("•")) {
                        break;
                    }

                    // 如果下一组是数字序号，停止合并
                    if (isNumberedItem(nextTextStr)) {
                        break;
                    }

                    // 合并当前组和下一组后的完整文本
                    String combinedText = text + " " + nextTextStr;

                    // 检查合并后的文本是否以句号结尾
                    char lastChar = combinedText.isEmpty() ? ' ' : combinedText.charAt(combinedText.length() - 1);
                    boolean endsWithPeriod = lastChar == '.' || lastChar == '!' || lastChar == '?';

                    // 如果合并后的文本以句号结尾，且下一组是大写字母开头，停止合并
                    if (endsWithPeriod && !nextTextStr.isEmpty() && Character.isUpperCase(nextTextStr.charAt(0))) {
                        System.out.println("  [DEBUG mergeListItems] 检测到句子结束(\"" + combinedText + "\") + 新句子开始(\"" + nextTextStr + "\")，停止合并");
                        break;
                    }

                    // 如果下一组是大写字母开头的新标题（非标点），停止合并
                    if (!nextTextStr.isEmpty() && Character.isUpperCase(nextTextStr.charAt(0))
                            && !nextTextStr.matches("^\\d+\\.[\\d]*[a-z]?\\s+.*")) {
                        // 检查是否是标题（不包含冒号或长度很短）
                        if (!nextTextStr.contains(":") && nextTextStr.length() < 30) {
                            break;
                        }
                    }

                    // 否则，合并到列表项组中
                    mergedListGroup.addAll(nextGroup);
                    mergedCount++;
                }

                mergedGroups.add(mergedListGroup);
                // 跳过已经被合并的组
                i += mergedCount;
            } else if (isNumberedItem(text)) {
                // 这是一个数字序号项，合并后续内容直到下一个数字序号或新标题
                List<CoordinateTextStripper.TextItem> mergedListGroup = new ArrayList<>(currentGroup);
                int mergedCount = 0; // 记录合并了多少个后续组

                // 继续查找后续内容
                for (int j = i + 1; j < groups.size(); j++) {
                    List<CoordinateTextStripper.TextItem> nextGroup = groups.get(j);

                    // 获取下一组的文本
                    StringBuilder nextText = new StringBuilder();
                    for (CoordinateTextStripper.TextItem item : nextGroup) {
                        nextText.append(item.text).append(" ");
                    }
                    String nextTextStr = nextText.toString().trim();

                    // 如果下一组也是数字序号，停止合并
                    if (isNumberedItem(nextTextStr)) {
                        break;
                    }

                    // 如果下一组以"•"开头，停止合并
                    if (nextTextStr.startsWith("•")) {
                        break;
                    }

                    // 合并当前组和下一组后的完整文本
                    String combinedText = text + " " + nextTextStr;

                    // 检查合并后的文本是否以句号结尾
                    char lastChar = combinedText.isEmpty() ? ' ' : combinedText.charAt(combinedText.length() - 1);
                    boolean endsWithPeriod = lastChar == '.' || lastChar == '!' || lastChar == '?';

                    // 如果合并后的文本以句号结尾，且下一组是大写字母开头，停止合并
                    if (endsWithPeriod && !nextTextStr.isEmpty() && Character.isUpperCase(nextTextStr.charAt(0))) {
                        System.out.println("  [DEBUG mergeListItems] 检测到数字序号句子结束(\"" + combinedText + "\") + 新句子开始(\"" + nextTextStr + "\")，停止合并");
                        break;
                    }

                    // 如果下一组是大写字母开头的新标题（非标点），停止合并
                    if (!nextTextStr.isEmpty() && Character.isUpperCase(nextTextStr.charAt(0))
                            && !nextTextStr.matches("^\\d+\\.[\\d]*[a-z]?\\s+.*")) {
                        // 检查是否是标题（不包含冒号或长度很短）
                        if (!nextTextStr.contains(":") && nextTextStr.length() < 30) {
                            break;
                        }
                    }

                    // 否则，合并到数字序号项组中
                    mergedListGroup.addAll(nextGroup);
                    mergedCount++;
                }

                mergedGroups.add(mergedListGroup);
                // 跳过已经被合并的组
                i += mergedCount;
            } else {
                // 不是列表项，直接添加
                mergedGroups.add(currentGroup);
            }
        }

        return mergedGroups;
    }

    /**
     * 判断下一行是否是当前句子的延续（改进版 - 更智能和通用）
     * @param currentLine 当前行的文本项
     * @param nextLine 下一行的文本项
     * @param allTextItems 所有文本项（用于计算动态阈值）
     */
    private static boolean isContinuationOfSentence(List<CoordinateTextStripper.TextItem> currentLine,
                                                    List<CoordinateTextStripper.TextItem> nextLine,
                                                    List<CoordinateTextStripper.TextItem> allTextItems) {

        // 获取当前行的文本
        StringBuilder currentText = new StringBuilder();
        for (CoordinateTextStripper.TextItem item : currentLine) {
            currentText.append(item.text).append(" ");
        }
        String currentLineText = currentText.toString().trim();

        // 获取下一行的文本
        StringBuilder nextText = new StringBuilder();
        for (CoordinateTextStripper.TextItem item : nextLine) {
            nextText.append(item.text).append(" ");
        }
        String nextLineText = nextText.toString().trim();

        // 检查当前行是否以不完整的单词结尾
        if (currentLineText.isEmpty() || nextLineText.isEmpty()) {
            return false;
        }

        // 获取下一行的第一个字符（跳过空格、标点和分段符号"n"）
        char nextFirstChar = ' ';
        String trimmedNextLine = nextLineText.trim();

        // 检查是否是单独的"n"（分段符号）
        if (trimmedNextLine.equals("n")) {
            // 这是单独的分段符号"n"，不应该合并
            return false;
        }

        // 如果看到"n "（n后面跟空格），这是分行符号，应该分行不合并
        if (trimmedNextLine.startsWith("n ")) {
            // "n "是分行符号，不合并
            return false;
        }

        // 检查是否以"n"开头但后面直接跟字母（如"neuron"），这是正常单词，不是分行符号
        // 这种情况应该继续处理，不在这里返回false
        boolean skipLeadingN = false;
        if (trimmedNextLine.startsWith("n") && trimmedNextLine.length() > 1) {
            char afterN = trimmedNextLine.charAt(1);
            // 如果"n"后面直接跟着小写字母，这是正常单词（如"neuron"），不是分行符号
            if (Character.isLowerCase(afterN)) {
                // 这是正常单词，继续处理
                skipLeadingN = false;
            } else if (Character.isUpperCase(afterN) || Character.isDigit(afterN)) {
                // "n"后面直接跟大写字母或数字，可能是分段符号，跳过"n"
                skipLeadingN = true;
            }
        }

        int startIndex = skipLeadingN ? 1 : 0;
        for (int i = startIndex; i < nextLineText.length(); i++) {
            char c = nextLineText.charAt(i);
            if (Character.isLetter(c)) {
                nextFirstChar = c;
                break;
            }
        }

        // 特殊情况：当前行以"•"开头且内容很短（如"• practices"），下一行是完整句子
        // 这种情况下不应该合并
        if (currentLineText.startsWith("•")) {
            // 移除"•"后检查内容长度
            String contentAfterBullet = currentLineText.substring(1).trim();
            int wordCount = contentAfterBullet.split("\\s+").length;

            // 如果只有一个词（如"practices"），且下一行以小写字母开头
            if (wordCount <= 1 && Character.isLowerCase(nextFirstChar)) {
                // 检查下一行是否是完整的句子（包含句号、逗号等）
                if (nextLineText.contains(".") || nextLineText.contains(",") || nextLineText.length() > 10) {
                    return false; // 不合并
                }
            }
        }

        // ============================================
        // 动态计算Y坐标差异阈值（基于页面行高）
        // ============================================
        float dynamicYThreshold = calculateDynamicYThreshold(allTextItems);

        // ============================================
        // 检查坐标位置，确保两行非常相近
        // ============================================
        // 计算当前行的X坐标范围（左边界和右边界）
        float currentMinX = Float.MAX_VALUE;
        float currentMaxX = 0;
        float currentY = currentLine.get(0).y;
        for (CoordinateTextStripper.TextItem item : currentLine) {
            currentMinX = Math.min(currentMinX, item.x);
            currentMaxX = Math.max(currentMaxX, item.x + item.text.length() * 6); // 估算宽度
        }

        // 计算下一行的X坐标范围
        float nextMinX = Float.MAX_VALUE;
        float nextMaxX = 0;
        float nextY = nextLine.get(0).y;
        for (CoordinateTextStripper.TextItem item : nextLine) {
            nextMinX = Math.min(nextMinX, item.x);
            nextMaxX = Math.max(nextMaxX, item.x + item.text.length() * 6); // 估算宽度
        }

        // 计算Y坐标差异
        float yDifference = Math.abs(currentY - nextY);

        // 计算X坐标的相似度（检查左对齐或接近对齐）
        float xDifference = Math.abs(currentMinX - nextMinX);

        // 规则0：如果Y坐标差异过大（超过动态阈值），说明不是同一段落的连续行
        if (yDifference > dynamicYThreshold) {
            return false;
        }

        // 规则0.5：如果X坐标差异过大（超过50像素），说明不是同一行的延续
        // 但允许一定的缩进（下一行X坐标稍大）
        if (xDifference > 50 && nextMinX < currentMinX - 15) {
            // 如果下一行明显左移（超过15像素），说明不是同一行的延续
            return false;
        }

        // 获取当前行的最后一个字符
        char lastChar = currentLineText.charAt(currentLineText.length() - 1);

        // ============================================
        // 基于文本内容的智能判断（优先级最高）
        // ============================================

        // 规则1: 当前行以连字符结尾，下一行以小写字母开头
        if (currentLineText.endsWith("-") && Character.isLowerCase(nextFirstChar)) {
            return true;
        }

        // 规则2: 当前行以逗号、分号、冒号结尾，下一行以小写字母开头
        if (isContinuationPunctuation(lastChar) && Character.isLowerCase(nextFirstChar)) {
            return true;
        }

        // 规则3: 当前行不以句号、问号、感叹号结尾，且下一行以小写字母开头
        // 这是最常见的跨行句子情况
        if (!isSentenceEndingPunctuation(lastChar) && Character.isLowerCase(nextFirstChar)) {
            // 额外检查：确保不是标题或独立短语
            // 如果当前行很短（少于8个字符）且下一行也很短（少于8个字符），可能是独立的短语，不合并
            if (currentLineText.length() < 8 && nextLineText.length() < 8) {
                return false;
            }

            // 检查是否是标题（全大写或首字母大写且很短）
            if (currentLineText.length() < 30 && Character.isUpperCase(currentLineText.charAt(0))) {
                // 检查是否全是大写字母（可能是标题）
                boolean allUpperCase = true;
                for (char c : currentLineText.toCharArray()) {
                    if (Character.isLetter(c) && !Character.isUpperCase(c)) {
                        allUpperCase = false;
                        break;
                    }
                }
                if (allUpperCase) {
                    return false; // 标题不合并
                }
            }

            return true;
        }

        // 规则4: 如果下一行以大写字母开头，且当前行以句号结尾，说明是新的句子，不应该合并
        if (Character.isUpperCase(nextFirstChar) && isSentenceEndingPunctuation(lastChar)) {
            return false;
        }

        // 规则5: 如果Y坐标差异在合理范围内，且满足其他条件
        if (yDifference >= 10 && yDifference <= dynamicYThreshold) {
            // 检查是否是缩进文本（下一行X坐标比当前行大，但差异不大）
            if (nextMinX > currentMinX - 15 && nextMinX < currentMinX + 40 && !isSentenceEndingPunctuation(lastChar)) {
                // 如果下一行以小写字母开头，可能是段落延续
                if (Character.isLowerCase(nextFirstChar)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * 计算动态Y坐标差异阈值（基于页面行高）
     * 通过分析所有文本项的Y坐标分布，计算典型的行间距
     */
    private static float calculateDynamicYThreshold(List<CoordinateTextStripper.TextItem> allTextItems) {
        if (allTextItems == null || allTextItems.size() < 2) {
            return 50.0f; // 默认阈值
        }

        // 收集所有Y坐标
        List<Float> yCoords = new ArrayList<>();
        for (CoordinateTextStripper.TextItem item : allTextItems) {
            yCoords.add(item.y);
        }
        Collections.sort(yCoords);

        // 计算相邻Y坐标的差异（行间距）
        List<Float> yDiffs = new ArrayList<>();
        for (int i = 1; i < yCoords.size(); i++) {
            float diff = Math.abs(yCoords.get(i) - yCoords.get(i - 1));
            // 过滤掉异常值：行间距应该在5-100像素之间
            if (diff >= 5 && diff <= 100) {
                yDiffs.add(diff);
            }
        }

        if (yDiffs.isEmpty()) {
            return 50.0f; // 默认阈值
        }

        // 计算中位数作为典型行间距
        Collections.sort(yDiffs);
        int mid = yDiffs.size() / 2;
        float medianLineHeight = yDiffs.get(mid);

        // 使用中位数的2.5倍作为阈值（允许更大的行间距变化）
        // 但限制在30-80像素之间，确保不会太宽松或太严格
        float threshold = Math.max(30.0f, Math.min(80.0f, medianLineHeight * 2.5f));

        return threshold;
    }

    /**
     * 判断字符是否是句子结束标点
     */
    private static boolean isSentenceEndingPunctuation(char c) {
        return c == '.' || c == '!' || c == '?' || c == ';';
    }

    /**
     * 判断字符是否是延续标点
     */
    private static boolean isContinuationPunctuation(char c) {
        return c == ',' || c == ':' || c == ';' || c == '-';
    }

    /**
     * 判断文本是否以数字序号开头（如1. 2. 3. 4.）
     */
    private static boolean isNumberedItem(String text) {
        if (text == null || text.isEmpty()) {
            return false;
        }
        // 使用正则表达式检查是否以数字序号开头
        return text.matches("^\\d+[.)]\\s+.*");
    }

    /**
     * 并行翻译多个文本 - 使用线程池同时处理多个翻译请求
     * 当批量翻译失败时，使用此方法可以大幅提升速度
     */
    private static List<String> translateParallel(List<String> texts, String from, String to) {
        List<String> results = new ArrayList<>(Collections.nCopies(texts.size(), ""));

        // 根据文本数量动态调整线程数（最多10个线程，避免过多并发导致API限流）
        int threadCount = Math.min(texts.size(), 10);
        ExecutorService executor = Executors.newFixedThreadPool(threadCount);

        try {
            List<Future<String>> futures = new ArrayList<>();

            // 提交所有翻译任务
            for (int i = 0; i < texts.size(); i++) {
                final int index = i;
                final String text = texts.get(i);
                Future<String> future = executor.submit(new Callable<String>() {
                    @Override
                    public String call() {
                        try {
                            return translateWithSmartAPI(text, from, to);
                        } catch (Exception e) {
                            System.err.println("⚠️ 并行翻译失败 [" + index + "]: " + e.getMessage());
                            return text; // 失败时返回原文
                        }
                    }
                });
                futures.add(future);
            }

            // 等待所有任务完成并收集结果
            for (int i = 0; i < futures.size(); i++) {
                try {
                    results.set(i, futures.get(i).get());
                } catch (InterruptedException | ExecutionException e) {
                    System.err.println("⚠️ 获取翻译结果失败 [" + i + "]: " + e.getMessage());
                    results.set(i, texts.get(i)); // 失败时返回原文
                }
            }

        } finally {
            executor.shutdown();
            try {
                // 等待所有任务完成，最多等待5分钟
                if (!executor.awaitTermination(5, TimeUnit.MINUTES)) {
                    executor.shutdownNow();
                }
            } catch (InterruptedException e) {
                executor.shutdownNow();
                Thread.currentThread().interrupt();
            }
        }

        return results;
    }

    /**
     * 批量翻译功能 - 将多个文本合并翻译以提高效率
     */
    private static List<String> translateBatch(List<String> texts, String from, String to) {
        List<String> results = new ArrayList<>();

        // 如果文本数量少，直接单个翻译
        if (texts.size() <= 3) {
            for (String text : texts) {
                results.add(translateWithSmartAPI(text, from, to));
            }
            return results;
        }

        // 批量翻译：将多个短文本合并
        StringBuilder batchText = new StringBuilder();
        List<Integer> textLengths = new ArrayList<>();

        for (String text : texts) {
            if (batchText.length() > 0) {
                batchText.append(" ||| "); // 使用分隔符
            }
            batchText.append(text);
            textLengths.add(text.length());
        }

        try {
            String batchResult = translateWithSmartAPI(batchText.toString(), from, to);
            String[] translatedParts = batchResult.split(" \\|\\|\\| ");

            for (int i = 0; i < texts.size() && i < translatedParts.length; i++) {
                results.add(translatedParts[i].trim());
            }

            // 如果分割失败，回退到并行翻译
            if (results.size() != texts.size()) {
                results.clear();
                results = translateParallel(texts, from, to);
            }
        } catch (Exception e) {
            // 批量翻译失败，回退到并行翻译
            results = translateParallel(texts, from, to);
        }

        return results;
    }

    /**
     * 智能翻译API选择
     * 优先级：DeepSeek > DeepL > MyMemory
     * 根据TranslationConfig中的配置自动选择可用的翻译服务
     */
    static String translateWithSmartAPI(String text, String from, String to) {
        // 优先使用DeepSeek翻译（AI模型，翻译质量更高）
        if (TranslationConfig.isDeepSeekConfigured()) {
            try {
                String result = translateWithDeepSeek(text, from, to);
                if (result != null && !result.equals(text) && !result.startsWith("翻译失败")) {
                    return result;
                }
            } catch (Exception e) {
                // 静默失败，尝试备选方案
            }
        }

        // 备选：使用DeepL翻译（优化：减少日志输出）
        if (TranslationConfig.isDeepLConfigured()) {
            try {
                String result = translateWithDeepL(text, from, to);
                if (result != null && !result.equals(text) && !result.startsWith("翻译失败")) {
                    return result;
                }
            } catch (Exception e) {
                // 静默失败，尝试备选方案
            }
        }

        // 备选：使用MyMemory翻译
        if (TranslationConfig.ENABLE_MYMEMORY) {
            try {
                String result = translateWithMyMemory(text, from, to);
                if (result != null && !result.equals(text) && !result.startsWith("翻译失败")) {
                    return result;
                }
            } catch (Exception e) {
                // 静默失败
            }
        }

        // 所有翻译都失败，返回原文
        return text;
    }

    // ============================================================
    // 词汇本：高频词统计（用于小程序 glossary 返回）
    // ============================================================

    /** 本次翻译任务的英文词频（小写）。 */
    private static final java.util.concurrent.ConcurrentHashMap<String, Integer> GLOSSARY_FREQ =
            new java.util.concurrent.ConcurrentHashMap<>();

    /** 常见停用词（可按需扩展）。 */
    private static final java.util.Set<String> GLOSSARY_STOPWORDS = new java.util.HashSet<>(java.util.Arrays.asList(
            "the","a","an","and","or","but","if","then","else","for","to","of","in","on","at","by","with","as",
            "is","are","was","were","be","been","being","this","that","these","those","it","its","we","you","they",
            "i","he","she","him","her","them","our","your","their","from","into","over","under","between","within",
            "not","no","yes","can","could","should","would","may","might","will","shall","do","does","did","done",
            "have","has","had","having","than","such","also","more","most","less","least","one","two","three",
            "use","using","used","based","data","figure","table","page"
    ));

    /** 兼容接口：本版本未实现翻译缓存，保留空实现避免编译错误。 */
    public static void clearTranslationCache() {
        // no-op
    }

    /** 清空本次任务的词频统计。 */
    public static void clearGlossaryCollector() {
        GLOSSARY_FREQ.clear();
    }

    /** 观察英文文本并累计词频（启发式：仅统计 a-z 单词，长度≥3）。 */
    public static void observeEnglishTextForGlossary(String text) {
        if (text == null || text.isEmpty()) return;
        java.util.regex.Matcher m = java.util.regex.Pattern.compile("[A-Za-z]{3,}").matcher(text);
        while (m.find()) {
            String w = m.group().toLowerCase();
            if (GLOSSARY_STOPWORDS.contains(w)) continue;
            GLOSSARY_FREQ.merge(w, 1, Integer::sum);
        }
    }

    /** 从词频统计生成 glossary：[{en, zh, count}, ...] */
    public static java.util.List<java.util.Map<String, Object>> buildGlossaryFromCollector(int maxTerms) {
        int limit = Math.max(1, Math.min(50, maxTerms));
        java.util.List<java.util.Map.Entry<String, Integer>> list = new java.util.ArrayList<>(GLOSSARY_FREQ.entrySet());
        list.sort((a, b) -> Integer.compare(b.getValue(), a.getValue()));

        java.util.List<java.util.Map<String, Object>> out = new java.util.ArrayList<>();
        for (int i = 0; i < list.size() && out.size() < limit; i++) {
            String termEn = list.get(i).getKey();
            int count = list.get(i).getValue();
            String termZh = translateWithSmartAPI(termEn, "en", "zh");
            java.util.Map<String, Object> one = new java.util.HashMap<>();
            one.put("en", termEn);
            one.put("zh", termZh != null ? termZh : "");
            one.put("count", count);
            out.add(one);
        }
        return out;
    }

    /** 兼容接口：本版本无缓存统计，直接回退到 collector。 */
    public static java.util.List<java.util.Map<String, Object>> buildGlossaryFromCache(int maxTerms) {
        return buildGlossaryFromCollector(maxTerms);
    }

    // ============================================================
    // 翻译API实现
    // ============================================================

    /**
     * DeepSeek翻译API - AI模型翻译，提供更准确的翻译结果
     * 需要API密钥，请在TranslationConfig中配置
     * 获取API密钥：https://platform.deepseek.com/
     */
    private static String translateWithDeepSeek(String text, String from, String to) throws Exception {
        // 从配置类获取API密钥
        if (!TranslationConfig.isDeepSeekConfigured()) {
            throw new Exception("请先在TranslationConfig中设置DeepSeek API密钥");
        }

        String apiKey = TranslationConfig.DEEPSEEK_API_KEY;

        // 语言代码转换（DeepSeek使用标准语言代码）
        String sourceLang = from.equals("en") ? "English" : from;
        String targetLang = to.equals("zh") ? "Chinese" : to;

        // 构建翻译提示词（优化：简化提示词以提高速度）
        String prompt = String.format(
                "翻译为%s：\n%s",
                targetLang, text
        );

        // DeepSeek API端点
        String url = "https://api.deepseek.com/v1/chat/completions";

        // 构建JSON请求体
        com.google.gson.JsonObject requestBody = new com.google.gson.JsonObject();
        requestBody.addProperty("model", TranslationConfig.DEEPSEEK_MODEL);
        requestBody.addProperty("temperature", TranslationConfig.DEEPSEEK_TEMPERATURE);

        com.google.gson.JsonArray messages = new com.google.gson.JsonArray();
        com.google.gson.JsonObject message = new com.google.gson.JsonObject();
        message.addProperty("role", "user");
        message.addProperty("content", prompt);
        messages.add(message);
        requestBody.add("messages", messages);

        requestBody.addProperty("max_tokens", TranslationConfig.DEEPSEEK_MAX_TOKENS_SINGLE);

        // 发送HTTP请求
        java.net.URL urlObj = new java.net.URI(url).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) urlObj.openConnection();
        connection.setRequestMethod("POST");
        connection.setRequestProperty("Content-Type", "application/json");
        connection.setRequestProperty("Authorization", "Bearer " + apiKey);
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(TranslationConfig.DEEPSEEK_CONNECT_TIMEOUT);
        connection.setReadTimeout(TranslationConfig.DEEPSEEK_READ_TIMEOUT_SINGLE);
        connection.setDoOutput(true);

        // 发送POST数据
        try (java.io.OutputStream os = connection.getOutputStream()) {
            byte[] input = requestBody.toString().getBytes("UTF-8");
            os.write(input, 0, input.length);
        }

        int responseCode = connection.getResponseCode();
        if (responseCode == 200) {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getInputStream(), "UTF-8"));
            StringBuilder response = new StringBuilder();
            String line;
            while ((line = reader.readLine()) != null) {
                response.append(line);
            }
            reader.close();

            // 解析DeepSeek JSON响应
            com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(response.toString()).getAsJsonObject();

            if (!jsonResponse.has("choices")) {
                throw new Exception("DeepSeek响应中没有choices字段");
            }

            com.google.gson.JsonArray choices = jsonResponse.getAsJsonArray("choices");
            if (choices.size() == 0) {
                throw new Exception("DeepSeek响应中没有choices数据");
            }

            com.google.gson.JsonObject choice = choices.get(0).getAsJsonObject();
            if (!choice.has("message")) {
                throw new Exception("DeepSeek响应中没有message字段");
            }

            com.google.gson.JsonObject responseMessage = choice.getAsJsonObject("message");
            if (!responseMessage.has("content")) {
                throw new Exception("DeepSeek响应中没有content字段");
            }

            String translatedText = responseMessage.get("content").getAsString().trim();

            // 清理可能的提示词残留
            if (translatedText.contains("翻译结果：")) {
                translatedText = translatedText.substring(translatedText.indexOf("翻译结果：") + 5).trim();
            }
            if (translatedText.contains("原文：")) {
                translatedText = translatedText.substring(0, translatedText.indexOf("原文：")).trim();
            }

            return translatedText;
        } else {
            // 读取错误响应
            java.io.BufferedReader errorReader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getErrorStream(), "UTF-8"));
            StringBuilder errorResponse = new StringBuilder();
            String errorLine;
            while ((errorLine = errorReader.readLine()) != null) {
                errorResponse.append(errorLine);
            }
            errorReader.close();

            throw new Exception("DeepSeek API错误码: " + responseCode + ", 错误信息: " + errorResponse.toString());
        }
    }

    /**
     * DeepSeek批量翻译API - 支持一次翻译多个文本
     * 使用批量翻译可以提高效率，减少API调用次数
     * 优化：如果文本数量过多，自动拆分成多个批次并行处理
     */
    private static List<String> translateBatchWithDeepSeek(List<String> texts, String from, String to) throws Exception {
        // 从配置类获取API密钥
        if (!TranslationConfig.isDeepSeekConfigured()) {
            throw new Exception("请先在TranslationConfig中设置DeepSeek API密钥");
        }

        // 优化：如果文本数量超过20个，拆分成多个批次并行处理
        if (texts.size() > 20) {
            System.out.println("🔄 文本数量较多 (" + texts.size() + ")，拆分成多个批次并行处理...");
            int batchSize = 15; // 每批15个文本
            List<List<String>> batches = new ArrayList<>();
            for (int i = 0; i < texts.size(); i += batchSize) {
                int end = Math.min(i + batchSize, texts.size());
                batches.add(texts.subList(i, end));
            }

            // 并行处理所有批次
            ExecutorService executor = Executors.newFixedThreadPool(Math.min(batches.size(), 5));
            List<Future<List<String>>> futures = new ArrayList<>();

            for (List<String> batch : batches) {
                Future<List<String>> future = executor.submit(new Callable<List<String>>() {
                    @Override
                    public List<String> call() throws Exception {
                        return translateBatchWithDeepSeekSingle(batch, from, to);
                    }
                });
                futures.add(future);
            }

            // 收集所有结果
            List<String> results = new ArrayList<>();
            for (Future<List<String>> future : futures) {
                try {
                    results.addAll(future.get());
                } catch (Exception e) {
                    throw new Exception("批次翻译失败: " + e.getMessage());
                }
            }

            executor.shutdown();
            System.out.println("✅ 多批次并行翻译完成，共 " + results.size() + " 个结果");
            return results;
        }

        // 文本数量较少，直接批量翻译
        return translateBatchWithDeepSeekSingle(texts, from, to);
    }

    /**
     * DeepSeek批量翻译API - 单批次实现
     */
    private static List<String> translateBatchWithDeepSeekSingle(List<String> texts, String from, String to) throws Exception {
        String apiKey = TranslationConfig.DEEPSEEK_API_KEY;

        // 优化：只在批量翻译时输出一次日志
        if (texts.size() > 1) {
            System.out.println("🔄 DeepSeek批量翻译 " + texts.size() + " 个文本...");
        }

        // 语言代码转换
        String sourceLang = from.equals("en") ? "English" : from;
        String targetLang = to.equals("zh") ? "Chinese" : to;

        // 构建批量翻译提示词（优化：添加上下文信息以提高翻译准确性）
        StringBuilder batchText = new StringBuilder();
        for (int i = 0; i < texts.size(); i++) {
            batchText.append(i + 1).append(". ").append(texts.get(i)).append("\n");
        }

        // 优化：充分利用AI的上下文理解和推理能力，提高翻译准确性
        String prompt = String.format(
                "你是一位专业的翻译专家，需要翻译以下%d个%s文本为%s。这些文本来自同一文档的连续上下文。\n\n" +
                        "请按照以下步骤进行翻译：\n" +
                        "【第一步：上下文分析】\n" +
                        "首先，仔细阅读所有文本，理解它们之间的逻辑关系和上下文语境。特别注意：\n" +
                        "- 识别相邻文本中的相关词汇（如\"discipline\"和\"disciplined\"、\"engineer\"和\"engineering\"等）\n" +
                        "- 分析文本的主题和领域（如软件工程、历史背景等）\n" +
                        "- 注意文本的结构（标题、段落、列表等）\n\n" +
                        "【第二步：术语一致性检查】\n" +
                        "在翻译前，先识别所有相关术语，确保：\n" +
                        "- 同一词汇在不同位置保持一致的翻译\n" +
                        "- 相关词汇（如名词和形容词形式）的翻译保持一致性\n" +
                        "- 例如：如果\"discipline\"在上下文中与\"disciplined\"相关，应统一翻译为\"规范/纪律\"而非\"学科\"\n\n" +
                        "【第三步：多义词处理】\n" +
                        "对于多义词，请：\n" +
                        "- 分析上下文语境，选择最合适的翻译\n" +
                        "- 如果某个文本以冒号结尾，必须考虑下一句的语境来确定翻译\n" +
                        "- 参考相邻文本的含义来推断正确的词义\n\n" +
                        "【第四步：翻译执行】\n" +
                        "基于以上分析，进行准确、流畅的翻译。确保：\n" +
                        "- 翻译自然流畅，符合中文表达习惯\n" +
                        "- 保持术语一致性\n" +
                        "- 准确传达原文含义\n" +
                        "- 若句子明显为软件工程课件（如耦合、类名 Car/Traveler、Step 1/2），即使个别词疑似 OCR 残缺，也请结合整句补全合理含义后再译，勿把类名误译为泛指的「类」\n\n" +
                        "请按以下格式输出翻译结果（每行一个）：\n" +
                        "1. 翻译1\n" +
                        "2. 翻译2\n" +
                        "...\n\n" +
                        "待翻译文本：\n%s",
                texts.size(), sourceLang, targetLang, batchText.toString()
        );

        // DeepSeek API端点
        String url = "https://api.deepseek.com/v1/chat/completions";

        // 构建JSON请求体
        com.google.gson.JsonObject requestBody = new com.google.gson.JsonObject();
        requestBody.addProperty("model", TranslationConfig.DEEPSEEK_MODEL);
        requestBody.addProperty("temperature", TranslationConfig.DEEPSEEK_TEMPERATURE);

        com.google.gson.JsonArray messages = new com.google.gson.JsonArray();
        com.google.gson.JsonObject message = new com.google.gson.JsonObject();
        message.addProperty("role", "user");
        message.addProperty("content", prompt);
        messages.add(message);
        requestBody.add("messages", messages);

        requestBody.addProperty("max_tokens", TranslationConfig.DEEPSEEK_MAX_TOKENS_BATCH);

        // 发送HTTP请求
        java.net.URL urlObj = new java.net.URI(url).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) urlObj.openConnection();
        connection.setRequestMethod("POST");
        connection.setRequestProperty("Content-Type", "application/json");
        connection.setRequestProperty("Authorization", "Bearer " + apiKey);
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(TranslationConfig.DEEPSEEK_CONNECT_TIMEOUT);
        connection.setReadTimeout(TranslationConfig.DEEPSEEK_READ_TIMEOUT_BATCH);
        connection.setDoOutput(true);

        // 发送POST数据
        try (java.io.OutputStream os = connection.getOutputStream()) {
            byte[] input = requestBody.toString().getBytes("UTF-8");
            os.write(input, 0, input.length);
        }

        int responseCode = connection.getResponseCode();
        if (responseCode == 200) {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getInputStream(), "UTF-8"));
            StringBuilder response = new StringBuilder();
            String responseLine;
            while ((responseLine = reader.readLine()) != null) {
                response.append(responseLine);
            }
            reader.close();

            // 解析DeepSeek JSON响应
            com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(response.toString()).getAsJsonObject();

            com.google.gson.JsonArray choices = jsonResponse.getAsJsonArray("choices");
            if (choices.size() == 0) {
                throw new Exception("DeepSeek批量翻译响应中没有choices数据");
            }

            com.google.gson.JsonObject choice = choices.get(0).getAsJsonObject();
            com.google.gson.JsonObject responseMessage = choice.getAsJsonObject("message");
            String translatedText = responseMessage.get("content").getAsString().trim();

            // 解析批量翻译结果（优化：支持更多格式以提高健壮性）
            List<String> results = new ArrayList<>();
            String[] lines = translatedText.split("\n");

            for (String line : lines) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) continue;

                // 匹配 "N. 翻译结果" 格式（支持中英文编号）
                if (trimmed.matches("\\d+\\.\\s*.*")) {
                    // 格式：1. 翻译结果 或 1．翻译结果（全角句号）
                    int dotIndex = trimmed.indexOf(".");
                    if (dotIndex == -1) {
                        dotIndex = trimmed.indexOf("．"); // 全角句号
                    }
                    if (dotIndex > 0 && dotIndex < trimmed.length() - 1) {
                        String result = trimmed.substring(dotIndex + 1).trim();
                        if (!result.isEmpty()) {
                            results.add(result);
                        }
                    }
                } else if (trimmed.matches("文本\\d+:.*") || trimmed.matches("文本\\d+：.*")) {
                    // 格式：文本1: 翻译结果 或 文本1：翻译结果（中文冒号）
                    int colonIndex = trimmed.indexOf(":");
                    if (colonIndex == -1) {
                        colonIndex = trimmed.indexOf("："); // 中文冒号
                    }
                    if (colonIndex > 0 && colonIndex < trimmed.length() - 1) {
                        String result = trimmed.substring(colonIndex + 1).trim();
                        if (!result.isEmpty()) {
                            results.add(result);
                        }
                    }
                } else if (trimmed.matches("^[\\d一二三四五六七八九十]+[.．、]\\s*.*")) {
                    // 格式：一. 翻译结果 或 1、翻译结果
                    int separatorIndex = -1;
                    for (int i = 0; i < trimmed.length(); i++) {
                        char c = trimmed.charAt(i);
                        if (c == '.' || c == '．' || c == '、') {
                            separatorIndex = i;
                            break;
                        }
                    }
                    if (separatorIndex > 0 && separatorIndex < trimmed.length() - 1) {
                        String result = trimmed.substring(separatorIndex + 1).trim();
                        if (!result.isEmpty()) {
                            results.add(result);
                        }
                    }
                } else if (!trimmed.startsWith("翻译") && !trimmed.startsWith("原文") &&
                        !trimmed.startsWith("文本") && !trimmed.startsWith("以下是") &&
                        !trimmed.startsWith("以下") && !trimmed.matches("^\\d+$")) {
                    // 直接是翻译结果（没有编号，且不是说明性文字）
                    results.add(trimmed);
                }
            }

            // 验证结果数量
            if (results.size() != texts.size()) {
                // 如果数量不匹配，输出调试信息并抛出异常，让上层回退到单个翻译
                System.out.println("⚠️ DeepSeek批量翻译结果数量不匹配（期望 " + texts.size() + " 个，实际 " + results.size() + " 个）");
                System.out.println("   实际返回内容: " + translatedText.substring(0, Math.min(200, translatedText.length())) + "...");
                System.out.println("   解析到的结果: " + results);
                System.out.println("   回退到单个翻译模式...");
                throw new Exception("批量翻译结果数量不匹配：期望 " + texts.size() + " 个，实际 " + results.size() + " 个");
            }

            // 优化：批量翻译成功时输出一次日志
            if (texts.size() > 1) {
                System.out.println("✅ DeepSeek批量翻译完成，共 " + results.size() + " 个结果");
            }

            return results;
        } else {
            // 读取错误响应
            java.io.BufferedReader errorReader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getErrorStream(), "UTF-8"));
            StringBuilder errorResponse = new StringBuilder();
            String errorLine;
            while ((errorLine = errorReader.readLine()) != null) {
                errorResponse.append(errorLine);
            }
            errorReader.close();

            throw new Exception("DeepSeek批量翻译API错误码: " + responseCode + ", 错误信息: " + errorResponse.toString());
        }
    }

    /**
     * 使用DeepSeek API批量检测文本质量，过滤OCR乱码和无意义的文本
     * @param texts 待检测的文本列表
     * @return 布尔列表，true表示文本有意义，false表示文本无意义（乱码）
     */
    private static List<Boolean> detectTextQualityWithDeepSeek(List<String> texts) throws Exception {
        String apiKey = TranslationConfig.DEEPSEEK_API_KEY;

        // 构建批量检测提示词
        StringBuilder batchText = new StringBuilder();
        for (int i = 0; i < texts.size(); i++) {
            batchText.append(i + 1).append(". ").append(texts.get(i)).append("\n");
        }

        // 使用明确的提示词，要求判断文本是否是OCR乱码或无意义的文本
        String prompt = String.format(
                "请严格判断以下%d个文本是否是OCR识别错误产生的乱码或无意义的文本。\n" +
                        "\n" +
                        "判断标准（严格模式）：\n" +
                        "1. 如果文本包含大量特殊字符、无意义的字符组合、无法理解的字符序列（如\"C—C\", \"NSN\", \"SSC\", \"___\"等），返回false\n" +
                        "2. 如果文本是明显的OCR乱码模式（如\"Ctéi'SSCSsSsSC\", \"C}NSN'N¥N\", \"NWNYNNNC\", \"CCstCSCSCS\"等），返回false\n" +
                        "3. 如果文本是课件上的真实内容（如完整的英文句子、有意义的单词、标题等），返回true\n" +
                        "4. 如果文本虽然包含一些OCR错误但整体是有意义的英文内容，返回true\n" +
                        "5. 特别注意：包含大量重复特殊字符、无意义字符组合的文本必须返回false\n" +
                        "\n" +
                        "示例：\n" +
                        "\"C—C\"Ctéi'SSCSsSsSC'(\"('C}NSN'N¥N'N'NWNYNNNC___CCstCSCSCS\"\" 72\" -> false（明显乱码）\n" +
                        "\"A model is a function M that takes as input the feature\" -> true（有意义的英文句子）\n" +
                        "\"Supervised Learning\" -> true（有意义的标题）\n" +
                        "\n" +
                        "请只返回%d个布尔值，每行一个，格式：\n" +
                        "true\n" +
                        "false\n" +
                        "true\n" +
                        "...\n" +
                        "\n" +
                        "文本列表：\n%s",
                texts.size(), texts.size(), batchText.toString()
        );

        // DeepSeek API端点
        String url = "https://api.deepseek.com/v1/chat/completions";

        // 构建JSON请求体
        com.google.gson.JsonObject requestBody = new com.google.gson.JsonObject();
        requestBody.addProperty("model", TranslationConfig.DEEPSEEK_MODEL);
        requestBody.addProperty("temperature", 0.1); // 低温度以获得更稳定的结果

        com.google.gson.JsonArray messages = new com.google.gson.JsonArray();
        com.google.gson.JsonObject message = new com.google.gson.JsonObject();
        message.addProperty("role", "user");
        message.addProperty("content", prompt);
        messages.add(message);
        requestBody.add("messages", messages);

        requestBody.addProperty("max_tokens", 500); // 只需要返回布尔值，不需要太多token

        // 发送HTTP请求
        java.net.URL urlObj = new java.net.URI(url).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) urlObj.openConnection();
        connection.setRequestMethod("POST");
        connection.setRequestProperty("Content-Type", "application/json");
        connection.setRequestProperty("Authorization", "Bearer " + apiKey);
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(TranslationConfig.DEEPSEEK_CONNECT_TIMEOUT);
        connection.setReadTimeout(15000); // 15秒超时
        connection.setDoOutput(true);

        // 发送POST数据
        try (java.io.OutputStream os = connection.getOutputStream()) {
            byte[] input = requestBody.toString().getBytes("UTF-8");
            os.write(input, 0, input.length);
        }

        int responseCode = connection.getResponseCode();
        if (responseCode == 200) {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getInputStream(), "UTF-8"));
            StringBuilder response = new StringBuilder();
            String responseLine;
            while ((responseLine = reader.readLine()) != null) {
                response.append(responseLine);
            }
            reader.close();

            // 解析DeepSeek JSON响应
            com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(response.toString()).getAsJsonObject();

            com.google.gson.JsonArray choices = jsonResponse.getAsJsonArray("choices");
            if (choices.size() == 0) {
                throw new Exception("DeepSeek文本质量检测响应中没有choices数据");
            }

            com.google.gson.JsonObject choice = choices.get(0).getAsJsonObject();
            com.google.gson.JsonObject responseMessage = choice.getAsJsonObject("message");
            String resultText = responseMessage.get("content").getAsString().trim();

            // 解析布尔值结果
            List<Boolean> results = new ArrayList<>();
            String[] lines = resultText.split("\n");

            for (String line : lines) {
                String trimmed = line.trim().toLowerCase();
                if (trimmed.isEmpty()) continue;

                // 解析布尔值
                if (trimmed.equals("true") || trimmed.equals("1") || trimmed.startsWith("true")) {
                    results.add(true);
                } else if (trimmed.equals("false") || trimmed.equals("0") || trimmed.startsWith("false")) {
                    results.add(false);
                } else {
                    // 如果无法解析，默认认为文本有意义（保守策略，避免误删）
                    results.add(true);
                }
            }

            // 如果结果数量不匹配，用true填充（保守策略）
            while (results.size() < texts.size()) {
                results.add(true);
            }

            return results;
        } else {
            // 读取错误响应
            java.io.BufferedReader errorReader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getErrorStream(), "UTF-8"));
            StringBuilder errorResponse = new StringBuilder();
            String errorLine;
            while ((errorLine = errorReader.readLine()) != null) {
                errorResponse.append(errorLine);
            }
            errorReader.close();

            throw new Exception("DeepSeek文本质量检测API错误码: " + responseCode + ", 错误信息: " + errorResponse.toString());
        }
    }

    /**
     * 本地预过滤：检测文本是否是明显的OCR乱码
     * 使用规则快速过滤明显的乱码，减少DeepSeek API调用
     * @param text 待检测的文本
     * @return true表示可能是乱码，false表示可能是有效文本
     */
    private static boolean isLikelyGarbageText(String text) {
        if (text == null || text.trim().isEmpty()) {
            return true;
        }

        String trimmed = text.trim();

        // 规则1: 如果文本太短（少于3个字符），可能是乱码
        if (trimmed.length() < 3) {
            // 但保留常见的短文本（如"TV", "OK", "No"等）
            String[] commonShortWords = {"TV", "OK", "No", "Yes", "Hi", "By", "To", "In", "On", "At", "We", "It", "Is", "Be", "Do", "Go", "Up", "If", "Or", "As", "So", "My", "Me", "He", "She", "Us", "Am", "An", "As", "Of", "To", "A", "I"};
            for (String word : commonShortWords) {
                if (trimmed.equalsIgnoreCase(word)) {
                    return false;
                }
            }
            // 如果包含大量特殊字符，可能是乱码
            int specialCharCount = 0;
            for (char c : trimmed.toCharArray()) {
                if (!Character.isLetterOrDigit(c) && !Character.isWhitespace(c)) {
                    specialCharCount++;
                }
            }
            if (specialCharCount > trimmed.length() / 2) {
                return true;
            }
        }

        // 规则2: 计算特殊字符比例
        int totalChars = trimmed.length();
        int letterCount = 0;
        int digitCount = 0;
        int specialCharCount = 0;
        int spaceCount = 0;

        for (char c : trimmed.toCharArray()) {
            if (Character.isLetter(c)) {
                letterCount++;
            } else if (Character.isDigit(c)) {
                digitCount++;
            } else if (Character.isWhitespace(c)) {
                spaceCount++;
            } else {
                specialCharCount++;
            }
        }

        // 如果特殊字符占比超过40%，可能是乱码
        if (totalChars > 0 && (float)specialCharCount / totalChars > 0.4f) {
            return true;
        }

        // 规则3: 如果字母占比太低（少于20%），可能是乱码
        if (totalChars > 5 && (float)letterCount / totalChars < 0.2f) {
            return true;
        }

        // 规则4: 检测明显的乱码模式
        // 包含大量重复的特殊字符组合
        if (trimmed.matches(".*[—\"'C]{3,}.*") ||
                trimmed.matches(".*[NSN]{3,}.*") ||
                trimmed.matches(".*[SC]{4,}.*") ||
                trimmed.matches(".*[___]{2,}.*")) {
            return true;
        }

        // 规则5: 检测无意义的字符序列
        // 如果包含大量连续的特殊字符（如 "C—C", "NSN", "SSC" 等）
        if (trimmed.matches(".*[^a-zA-Z0-9\\s]{3,}[^a-zA-Z0-9\\s]{3,}.*")) {
            // 但排除常见的标点符号组合
            if (!trimmed.matches(".*\\.\\.\\..*") && // 排除 "..."
                    !trimmed.matches(".*--.*") && // 排除 "--"
                    !trimmed.matches(".*''.*")) { // 排除 "'"
                return true;
            }
        }

        // 规则6: 检测特定的乱码模式（基于实际观察到的乱码）
        String[] garbagePatterns = {
                "C—C", "Ctéi", "SSCSsSsSC", "C}NSN", "N¥N", "NWNYNNNC", "CCstCSCSCS",
                "TTTC", "C*isSsSC", "CSNCSCsSCSCSCSCSCSCSCSCSCSCSCSCSCSCSsSsS",
                "PAO iG", "PIO K HE", "Hh K PIAOH KE", "x21 0iH KE", "O nxz"
        };

        for (String pattern : garbagePatterns) {
            if (trimmed.contains(pattern)) {
                // 如果文本主要是这个模式，肯定是乱码
                if (trimmed.length() <= pattern.length() * 2) {
                    return true;
                }
                // 如果这个模式在文本中占比很大，也是乱码
                int patternCount = 0;
                int index = 0;
                while ((index = trimmed.indexOf(pattern, index)) != -1) {
                    patternCount++;
                    index += pattern.length();
                }
                if (patternCount * pattern.length() > trimmed.length() * 0.3) {
                    return true;
                }
            }
        }

        // 规则7: 如果文本以数字结尾且前面是乱码字符，可能是乱码
        if (trimmed.matches(".*[^a-zA-Z0-9\\s]{5,}\\s*\\d+$")) {
            return true;
        }

        // 规则8: 检测是否包含大量非ASCII字符（可能是OCR错误）
        int nonAsciiCount = 0;
        for (char c : trimmed.toCharArray()) {
            if (c > 127 && !Character.isLetterOrDigit(c)) {
                nonAsciiCount++;
            }
        }
        if (nonAsciiCount > totalChars * 0.3f && totalChars > 10) {
            return true;
        }

        // 规则9: 幻灯片项目符号 ❑/■ 等常被 OCR 成 UO)、LU)、L)、O)、PE) 等极短串，勿送翻译（易误译为校名等）
        if (trimmed.length() <= 5 && trimmed.matches("(?i)^(uo|lu)\\)$")
                || trimmed.matches("(?i)^l\\)$")
                || trimmed.matches("(?i)^[o0q]\\)$")
                || trimmed.matches("(?i)^pe\\)$")) {
            return true;
        }

        // 如果通过所有检查，认为可能是有效文本
        return false;
    }

    private static int countCharOccurrences(String s, char ch) {
        if (s == null) {
            return 0;
        }
        int n = 0;
        for (int i = 0; i < s.length(); i++) {
            if (s.charAt(i) == ch) {
                n++;
            }
        }
        return n;
    }

    private static int countNonWhitespaceChars(String s) {
        if (s == null) {
            return 0;
        }
        int n = 0;
        for (int i = 0; i < s.length(); i++) {
            if (!Character.isWhitespace(s.charAt(i))) {
                n++;
            }
        }
        return n;
    }

    private static int countNonLetterDigitNonSpace(String s) {
        if (s == null) {
            return 0;
        }
        int n = 0;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (!Character.isWhitespace(c) && !Character.isLetterOrDigit(c)) {
                n++;
            }
        }
        return n;
    }

    private static int countCjkUnifiedIdeographs(String s) {
        if (s == null) {
            return 0;
        }
        int n = 0;
        for (int i = 0; i < s.length(); ) {
            int cp = s.codePointAt(i);
            i += Character.charCount(cp);
            if ((cp >= 0x4E00 && cp <= 0x9FFF) || (cp >= 0x3400 && cp <= 0x4DBF)) {
                n++;
            }
        }
        return n;
    }

    /**
     * 状态机示意图、逻辑守卫等 OCR：含 up/down 与 ^¬、大量 / | \\、转移标注 |1|2 等，不应整段翻译进 PDF。
     */
    private static boolean isLikelyFsmDiagramOrLogicOcrNoise(String text) {
        if (text == null) {
            return false;
        }
        String t = text.trim();
        if (t.length() < 4 || t.length() > 220) {
            return false;
        }
        int score = 0;
        int bs = countCharOccurrences(t, '\\');
        int slash = countCharOccurrences(t, '/');
        int pipe = countCharOccurrences(t, '|');
        int caret = countCharOccurrences(t, '^');
        if (bs >= 2) {
            score += 3;
        }
        if (slash + pipe >= 5) {
            score += 4;
        } else if (slash + pipe >= 3) {
            score += 2;
        }
        if (caret >= 2) {
            score += 2;
        }
        if (Pattern.compile("(?i)(^|\\s)(up|down)\\s*[\\^∧]").matcher(t).find()) {
            score += 3;
        }
        if (Pattern.compile("(?i)down\\s*[\\^∧]").matcher(t).find()) {
            score += 2;
        }
        Matcher slashDigit = Pattern.compile("[/|]\\s*\\d").matcher(t);
        int sd = 0;
        while (slashDigit.find()) {
            sd++;
        }
        if (sd >= 1) {
            score += 2;
        }
        if (sd >= 2) {
            score += 2;
        }
        if (Pattern.compile("(?i)sup\\s+sup|:\\s*a\\s+e?S\\s+a\\s").matcher(t).find()) {
            score += 3;
        }
        int nonWs = countNonWhitespaceChars(t);
        int specials = countNonLetterDigitNonSpace(t);
        if (nonWs > 10 && specials * 4 >= nonWs) {
            score += 3;
        }
        int letters = countAsciiLatinLetters(t);
        if (letters <= 10 && (slash + pipe + bs + caret) >= 3 && t.length() < 85) {
            score += 2;
        }
        if (Pattern.compile("(?i)inputs?:.*\\b(up|down)\\b").matcher(t).find()
                && Pattern.compile("(?i)output").matcher(t).find()
                && (t.contains("{") || t.contains("}") || slash + pipe >= 2)) {
            score += 3;
        }
        if (Pattern.compile("\\{[^}]{0,40}\\d").matcher(t).find() && (slash > 0 || pipe > 0 || caret > 0)) {
            score += 2;
        }
        return score >= 5;
    }

    /**
     * 混合 OCR 译文：反斜杠、竖线、碎片拉丁、上/下与运算符混杂等，判为无意义机翻，不写入 PDF。
     */
    private static boolean isLikelyNonsenseHybridOcrChineseTranslation(String original, String translated) {
        if (translated == null) {
            return true;
        }
        String tr = translated.trim();
        if (tr.isEmpty()) {
            return true;
        }
        int len = tr.length();
        if (tr.contains("\\")) {
            return true;
        }
        int pipe = countCharOccurrences(tr, '|');
        if (pipe >= 2) {
            return true;
        }
        int slash = countCharOccurrences(tr, '/');
        if (slash >= 3 && len < 130) {
            return true;
        }
        if (Pattern.compile("(?i)\\b(oe|pia|kf|kk|ks)\\b").matcher(tr).find()) {
            return true;
        }
        if (tr.contains("oe ") || tr.contains(" PIA") || tr.contains("PIA ")) {
            return true;
        }
        int upDown = 0;
        for (int i = 0; i < tr.length(); ) {
            int cp = tr.codePointAt(i);
            i += Character.charCount(cp);
            if (cp == '上' || cp == '下') {
                upDown++;
            }
        }
        if (upDown >= 3 && (slash + pipe + bsCount(tr)) >= 2) {
            return true;
        }
        if (Pattern.compile("上\\s*[/\\\\]").matcher(tr).find() && len < 110) {
            return true;
        }
        int cjk = countCjkUnifiedIdeographs(tr);
        int lat = countAsciiLatinLetters(tr);
        if (len >= 10 && cjk < len * 0.14 && lat >= len * 0.17) {
            return true;
        }
        if (len <= 5 && lat >= 1 && cjk <= 2) {
            return true;
        }
        if (Pattern.compile("[\u4e00-\u9fff]{1}[/\\\\|]").matcher(tr).find() && pipe + slash >= 2) {
            return true;
        }
        if (isLikelyFsmDiagramOrLogicOcrNoise(original) && len <= 52 && cjk <= 18) {
            return true;
        }
        if (Pattern.compile("[—–-]{3,}").matcher(tr).find() && (pipe >= 1 || slash >= 2)) {
            return true;
        }
        if (len <= 4 && Pattern.compile("\\d").matcher(tr).find() && cjk == 0) {
            return true;
        }
        if (len < 18 && tr.startsWith("~")) {
            return true;
        }
        return false;
    }

    private static int bsCount(String s) {
        return countCharOccurrences(s, '\\');
    }

    /**
     * 检测单段文本是否主要为代码（如 Java/C++ 等源码）
     * 用于区分「纯代码组」与「讲解+代码混合段」：混合段会有自然语句特征，不判为代码
     */
    private static boolean isLikelyCodeSegment(String text) {
        if (text == null || text.length() < 15) return false;
        String t = text.trim();
        String lower = t.toLowerCase();
        int codeIndicators = 0;
        if (lower.contains("class ") || lower.contains("interface ")) codeIndicators++;
        if (lower.contains("public ") || lower.contains("private ") || lower.contains("void ")) codeIndicators++;
        if (t.contains("{") && t.contains("}")) codeIndicators++;
        if (t.contains(";") && (t.indexOf(';') != t.lastIndexOf(';') || t.length() > 30)) codeIndicators++;
        if (lower.contains("implements ") || lower.contains("extends ")) codeIndicators++;
        if (t.contains("()") || (t.contains("(") && t.contains(")"))) codeIndicators++;
        if (lower.contains("system.out") || lower.contains("println")) codeIndicators++;
        // 明显像自然语言（讲解中带少量代码）：句末标点或常见词
        boolean looksLikeProse = t.matches(".*[.!?]\\s*$") ||
                lower.matches(".*\\b(the|is|are|we|this|that|use|can|will|should|here|following)\\b.*");
        if (looksLikeProse) return codeIndicators >= 4; // 混合段需更高代码密度才判为代码
        return codeIndicators >= 3;
    }

    /**
     * Unicode 数学字母数字区（PDF 中常见的斜体 𝑭、𝑡 等）
     */
    private static boolean isMathematicalAlphanumeric(int cp) {
        return cp >= 0x1D400 && cp <= 0x1D7FF;
    }

    /**
     * 公式中常见的非 ASCII 符号：运算符、希腊字母、上下标、箭头等；含埃塞俄比亚文块（部分 PDF 误映射为导数符号）
     */
    private static boolean isFormulaSupportingCodePoint(int cp) {
        if (isMathematicalAlphanumeric(cp)) return true;
        if (cp >= 0x2200 && cp <= 0x22FF) return true;   // 数学运算符，如 ∫ ∀ ∂
        if (cp >= 0x2A00 && cp <= 0x2AFF) return true;   // 补充运算符
        if (cp >= 0x2100 && cp <= 0x214F) return true;   // 字母式符号
        if (cp >= 0x2190 && cp <= 0x21FF) return true;   // 箭头
        if (cp >= 0x2070 && cp <= 0x209F) return true;   // 上下标
        if (cp == 0x00B2 || cp == 0x00B3 || cp == 0x00B9) return true;
        if ((cp >= 0x0391 && cp <= 0x03A9) || (cp >= 0x03B1 && cp <= 0x03C9)) return true; // 希腊字母
        if (cp >= 0x1200 && cp <= 0x137F) return true;   // 埃塞俄比亚文（课件中常被误映射）
        if (cp >= 0x1380 && cp <= 0x1399) return true;
        return false;
    }

    private static int countAsciiLatinLetters(String s) {
        if (s == null) return 0;
        int n = 0;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) n++;
        }
        return n;
    }

    /**
     * 等式一侧是否仅由数学相关字符组成（允许少量 ASCII 变量名，如 sin、dt）
     */
    private static boolean equationSideMostlyMathTokens(String side) {
        if (side == null || side.isEmpty()) return true;
        int asciiLetters = 0;
        for (int i = 0; i < side.length(); ) {
            int cp = side.codePointAt(i);
            i += Character.charCount(cp);
            if (Character.isWhitespace(cp)) continue;
            if (isFormulaSupportingCodePoint(cp)) continue;
            if (Character.isDigit(cp)) continue;
            if (cp == '=' || cp == '+' || cp == '-' || cp == '*' || cp == '/' || cp == '^' ||
                    cp == '(' || cp == ')' || cp == '[' || cp == ']' || cp == '.' || cp == ',' ||
                    cp == ';' || cp == ':' || cp == '|' || cp == '!' || cp == '\'' || cp == '\u2032') continue;
            if (cp >= 'a' && cp <= 'z' || cp >= 'A' && cp <= 'Z') {
                asciiLetters++;
                continue;
            }
            return false;
        }
        return asciiLetters <= 10;
    }

    /**
     * 检测单段文本是否主要为数学公式/数字符号（不翻译且不放入翻译件，直接跳过）
     * 包括：LaTeX、MathML、Unicode 数学字母（𝑭𝑡）、积分希腊字母、纯数字算式、高密度数学符号等
     */
    private static boolean isLikelyMathOrFormula(String text) {
        if (text == null) return false;
        String t = text.trim();
        if (t.isEmpty()) return true;

        // LaTeX 常见标记
        if (t.contains("$") && (t.contains("\\") || t.matches(".*\\$[^$]+\\$.*") || t.matches(".*\\$\\$[^$]+\\$\\$.*"))) return true;
        if (t.contains("\\(") && t.contains("\\)")) return true;
        if (t.contains("\\[") && t.contains("\\]")) return true;
        if (t.contains("\\frac") || t.contains("\\sum") || t.contains("\\int") || t.contains("\\sqrt") ||
                t.contains("\\alpha") || t.contains("\\beta") || t.contains("\\theta") || t.contains("\\infty") ||
                t.contains("\\leq") || t.contains("\\geq") || t.contains("\\neq") || t.contains("\\approx")) return true;

        // MathML
        if (t.contains("<math") || t.contains("</math>")) return true;

        // 纯数字与常见数学标点（无自然语言）
        if (t.matches("^[0-9\\s.,;:=+\\-*/^()\\[\\]\\\\]+$") && t.length() <= 80) return true;
        if (t.matches("^[0-9.]+\\s*[=<>]\\s*[0-9.]+$")) return true;

        // 短等式：含 = 且两侧均为数学记号（含 Unicode 数学字母）
        if (t.length() <= 120 && t.contains("=")) {
            String[] sides = t.split("=", 2);
            if (sides.length == 2) {
                String left = sides[0].trim();
                String right = sides[1].trim();
                if (left.length() <= 60 && right.length() <= 60 &&
                        equationSideMostlyMathTokens(left) && equationSideMostlyMathTokens(right)) {
                    return true;
                }
            }
        }

        // 仍兼容仅 ASCII 的短等式
        if (t.length() <= 60 && t.contains("=")) {
            String[] sides = t.split("=", 2);
            if (sides.length == 2) {
                String left = sides[0].trim();
                String right = sides[1].trim();
                if (left.length() <= 25 && right.length() <= 25 &&
                        left.matches("^[a-zA-Z0-9^+\\-*/()\\s.]+$") &&
                        right.matches("^[a-zA-Z0-9^+\\-*/()\\s.]+$")) {
                    return true;
                }
            }
        }

        // 按码点统计：数学类字符占比高且几乎无普通英文句子字母 → 公式行/碎片
        int totalNonWs = 0;
        int formulaClass = 0;
        int mathAlphCount = 0;
        for (int i = 0; i < t.length(); ) {
            int cp = t.codePointAt(i);
            i += Character.charCount(cp);
            if (Character.isWhitespace(cp)) continue;
            totalNonWs++;
            if (isMathematicalAlphanumeric(cp)) {
                formulaClass++;
                mathAlphCount++;
                continue;
            }
            if (isFormulaSupportingCodePoint(cp)) {
                formulaClass++;
                continue;
            }
            if (Character.isDigit(cp)) {
                formulaClass++;
                continue;
            }
            if (cp == '=' || cp == '+' || cp == '-' || cp == '*' || cp == '/' || cp == '^' ||
                    cp == '(' || cp == ')' || cp == '[' || cp == ']' || cp == '.' || cp == ',' ||
                    cp == ';' || cp == ':' || cp == '<' || cp == '>' || cp == '\u2212' || cp == '\u00D7' ||
                    cp == '\u00F7' || cp == '\u221A' || cp == '\u221E' || cp == '\u2264' || cp == '\u2265' ||
                    cp == '\u2248' || cp == '\u2260' || cp == '\u2192' || cp == '\u2200') {
                formulaClass++;
            }
        }

        int asciiLat = countAsciiLatinLetters(t);
        if (totalNonWs > 0) {
            double ratio = (double) formulaClass / totalNonWs;
            // 整行几乎全是数学记号
            if (totalNonWs <= 80 && ratio >= 0.82 && asciiLat <= 3) return true;
            // 含 Unicode 数学字母、几乎无 ASCII 英文
            if (mathAlphCount >= 1 && asciiLat <= 2 && totalNonWs <= 50) return true;
            // 短串：单字母变量 𝑡、𝜏 等
            if (totalNonWs <= 4 && ratio >= 0.9) return true;
            if (totalNonWs >= 3 && totalNonWs <= 100 && ratio >= 0.72 && asciiLat <= 4 && t.contains("=")) return true;
        }

        // 数学符号密度（仅 ASCII 数字与运算符，原逻辑）
        int mathOrDigit = 0;
        int total = 0;
        for (int i = 0; i < t.length(); i++) {
            char c = t.charAt(i);
            if (Character.isWhitespace(c)) continue;
            total++;
            if (Character.isDigit(c)) { mathOrDigit++; continue; }
            if (c == '.' || c == ',' || c == ';' || c == '=' || c == '+' || c == '-' || c == '*' || c == '/' ||
                    c == '^' || c == '(' || c == ')' || c == '[' || c == ']' || c == '<' || c == '>' ||
                    c == '\u2212' || c == '\u00D7' || c == '\u00F7' || c == '\u221A' || c == '\u221E' ||
                    c == '\u2264' || c == '\u2265' || c == '\u2248' || c == '\u2260') {
                mathOrDigit++;
            }
        }
        if (total >= 3 && total <= 100 && (double) mathOrDigit / total >= 0.65) return true;

        return false;
    }

    /**
     * 译文仍为公式/纯符号，或原文为公式但误送入翻译时：不写入 PDF。
     * 混合嵌入图 OCR：再拦截状态图逻辑式原文，以及「中英符号混杂」的低质量译文。
     */
    private static boolean shouldSkipDrawingFormulaOrSymbolOnly(
            String original, String translated, boolean hybridEmbeddedImageOcrPass) {
        if (translated == null || translated.trim().isEmpty()) {
            return true;
        }
        if (isLikelyMathOrFormula(original)) {
            return true;
        }
        if (isLikelyMathOrFormula(translated)) {
            return true;
        }
        if (hybridEmbeddedImageOcrPass && isLikelyFsmDiagramOrLogicOcrNoise(original)) {
            return true;
        }
        if (hybridEmbeddedImageOcrPass && isLikelyNonsenseHybridOcrChineseTranslation(original, translated)) {
            return true;
        }
        return false;
    }

    /**
     * 判断是否应跳过绘制译文：
     * - 原文与译文在规范化后完全一致
     * - 文本看起来是代码段
     * - 但排除注释（Javadoc、// 行注释等），注释仍然需要翻译
     */
    private static boolean shouldSkipDrawingTranslation(String original, String translated) {
        if (original == null || translated == null) return false;
        String normOriginal = normalizeForCompare(original);
        String normTranslated = normalizeForCompare(translated);
        if (!normOriginal.equals(normTranslated)) return false;
        // 注释内容即便与原文相同也保留译文（后续可扩展为多语言注释）
        if (isCommentText(normOriginal)) return false;
        // 仅当主要为代码段时才跳过绘制
        return isLikelyCodeSegment(normOriginal);
    }

    /**
     * 规范化用于比较的文本：去除多余空白、统一换行等
     */
    private static String normalizeForCompare(String s) {
        if (s == null) return "";
        String t = s.replace("\r\n", "\n").replace('\r', '\n');
        // 将所有空白（空格、换行、制表符）折叠为单个空格
        t = t.replaceAll("\\s+", " ").trim();
        return t;
    }

    /**
     * 粗略判断一段文本是否为注释（Javadoc 或 行注释）。
     * 这些内容通常包含自然语言说明，仍然需要翻译。
     */
    private static boolean isCommentText(String text) {
        if (text == null) return false;
        String t = text.trim();
        // 仅保留 Javadoc 风格注释需要翻译：/** ... */ 以及块内以 * 开头的行
        if (t.startsWith("/**")) return true;
        if (t.startsWith("*") && !t.contains("{") && !t.contains("}")) return true;
        return false;
    }

    /**
     * 使用 DeepSeek 批量判断文本是否为「代码段」。
     * 返回列表中，true 表示对应文本应视为代码（不翻译或不绘制译文），false 表示普通文本。
     */
    private static List<Boolean> detectCodeSegmentsWithDeepSeek(List<String> texts) throws Exception {
        String apiKey = TranslationConfig.DEEPSEEK_API_KEY;

        StringBuilder batchText = new StringBuilder();
        for (int i = 0; i < texts.size(); i++) {
            batchText.append(i + 1).append(". ").append(texts.get(i)).append("\n");
        }

        String prompt = String.format(
                "你是一名代码与课件内容识别助手。现在有%d段来自编程课件的文本，请判断每一段是否主要是“代码片段”（如 Java/C/C++/Python 代码），还是说明性文字/标题/注释等。\n" +
                        "\n" +
                        "判断规则（严格）：\n" +
                        "1. 含有大量语句分号、花括号、函数定义、变量声明等，应视为代码。\n" +
                        "2. 仅包含自然语言句子、标题、列表说明的，视为非代码。\n" +
                        "3. Javadoc 或块注释（/** ... */ 内的自然语言）视为非代码。\n" +
                        "4. 行注释 // 后面如果主要是自然语言，可视为非代码。\n" +
                        "\n" +
                        "请只输出%d行，每行一个布尔值：true 或 false。\n" +
                        "true 表示“这一段主要是代码片段，应视为代码块”；false 表示“这一段主要是说明性文字或注释”。\n" +
                        "\n" +
                        "文本列表：\n%s",
                texts.size(), texts.size(), batchText.toString()
        );

        String url = "https://api.deepseek.com/v1/chat/completions";

        com.google.gson.JsonObject requestBody = new com.google.gson.JsonObject();
        requestBody.addProperty("model", TranslationConfig.DEEPSEEK_MODEL);
        requestBody.addProperty("temperature", 0.1);

        com.google.gson.JsonArray messages = new com.google.gson.JsonArray();
        com.google.gson.JsonObject message = new com.google.gson.JsonObject();
        message.addProperty("role", "user");
        message.addProperty("content", prompt);
        messages.add(message);
        requestBody.add("messages", messages);
        requestBody.addProperty("max_tokens", 500);

        java.net.URL urlObj = new java.net.URI(url).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) urlObj.openConnection();
        connection.setRequestMethod("POST");
        connection.setRequestProperty("Content-Type", "application/json");
        connection.setRequestProperty("Authorization", "Bearer " + apiKey);
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(TranslationConfig.DEEPSEEK_CONNECT_TIMEOUT);
        connection.setReadTimeout(15000);
        connection.setDoOutput(true);

        try (java.io.OutputStream os = connection.getOutputStream()) {
            byte[] input = requestBody.toString().getBytes("UTF-8");
            os.write(input, 0, input.length);
        }

        int responseCode = connection.getResponseCode();
        if (responseCode == 200) {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getInputStream(), "UTF-8"));
            StringBuilder response = new StringBuilder();
            String line;
            while ((line = reader.readLine()) != null) {
                response.append(line);
            }
            reader.close();

            com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(response.toString()).getAsJsonObject();
            com.google.gson.JsonArray choices = jsonResponse.getAsJsonArray("choices");
            if (choices == null || choices.size() == 0) {
                throw new Exception("DeepSeek 代码检测响应中没有 choices 数据");
            }
            com.google.gson.JsonObject choice = choices.get(0).getAsJsonObject();
            com.google.gson.JsonObject responseMessage = choice.getAsJsonObject("message");
            String resultText = responseMessage.get("content").getAsString().trim();

            List<Boolean> results = new ArrayList<>();
            String[] lines = resultText.split("\n");
            for (String l : lines) {
                String trimmed = l.trim().toLowerCase();
                if (trimmed.isEmpty()) continue;
                if (trimmed.equals("true") || trimmed.equals("1") || trimmed.startsWith("true")) {
                    results.add(true);
                } else if (trimmed.equals("false") || trimmed.equals("0") || trimmed.startsWith("false")) {
                    results.add(false);
                } else {
                    // 无法解析时按“非代码”处理，避免误删正常文字
                    results.add(false);
                }
            }
            // 若数量不足，补 false；若过多则截断
            while (results.size() < texts.size()) results.add(false);
            if (results.size() > texts.size()) {
                results = results.subList(0, texts.size());
            }
            return results;
        } else {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getErrorStream(), "UTF-8"));
            StringBuilder error = new StringBuilder();
            String line;
            while ((line = reader.readLine()) != null) {
                error.append(line);
            }
            reader.close();
            throw new Exception("DeepSeek 代码检测 API 错误码: " + responseCode + ", 错误信息: " + error.toString());
        }
    }

    /**
     * 检测当前页是否主要为代码页（绝大多数组都是代码）
     * 仅当大部分组为代码时才整页跳过；否则只跳过「主要为代码」的组，保留讲解+代码混合段的翻译
     */
    private static boolean isLikelyCodePage(List<List<CoordinateTextStripper.TextItem>> textGroups,
                                            java.util.Set<Integer> codeSegmentGroupIndices) {
        if (textGroups.isEmpty() || codeSegmentGroupIndices == null) return false;
        // 当 75% 以上的组被判定为代码段时，视为整页代码页
        double ratio = (double) codeSegmentGroupIndices.size() / textGroups.size();
        return ratio >= 0.75;
    }

    /**
     * DeepL翻译API
     * 需要API密钥，请替换为你的实际API密钥
     */
    /**
     * DeepL批量翻译API - 支持一次翻译多个文本
     */
    private static List<String> translateBatchWithDeepL(List<String> texts, String from, String to) throws Exception {
        // 从配置类获取API密钥
        if (!TranslationConfig.isDeepLConfigured()) {
            throw new Exception("请先在TranslationConfig中设置DeepL API密钥");
        }

        String apiKey = TranslationConfig.DEEPL_API_KEY;

        // 优化：只在批量翻译时输出一次日志
        if (texts.size() > 1) {
            System.out.println("🔄 批量翻译 " + texts.size() + " 个文本...");
        }

        // 语言代码转换
        String sourceLang = from.equals("en") ? "EN" : from.toUpperCase();
        String targetLang = to.equals("zh") ? "ZH" : to.toUpperCase();

        // 使用DeepL Pro API端点，支持批量翻译
        String url = "https://api.deepl-pro.com/v2/translate";
        StringBuilder postData = new StringBuilder("auth_key=" + apiKey +
                "&source_lang=" + sourceLang +
                "&target_lang=" + targetLang);

        // 添加多个text参数
        for (String text : texts) {
            postData.append("&text=").append(java.net.URLEncoder.encode(text, "UTF-8"));
        }

        java.net.URL urlObj = new java.net.URI(url).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) urlObj.openConnection();
        connection.setRequestMethod("POST");
        connection.setRequestProperty("Content-Type", "application/x-www-form-urlencoded");
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(8000); // 优化：减少超时时间到8秒
        connection.setReadTimeout(10000); // 优化：读取超时10秒
        connection.setDoOutput(true);

        // 发送POST数据
        try (java.io.OutputStream os = connection.getOutputStream()) {
            byte[] input = postData.toString().getBytes("UTF-8");
            os.write(input, 0, input.length);
        }

        int responseCode = connection.getResponseCode();
        if (responseCode == 200) {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getInputStream(), "UTF-8"));
            StringBuilder response = new StringBuilder();
            String line;
            while ((line = reader.readLine()) != null) {
                response.append(line);
            }
            reader.close();

            // 解析DeepL JSON响应
            com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(response.toString()).getAsJsonObject();
            com.google.gson.JsonArray translations = jsonResponse.getAsJsonArray("translations");
            List<String> results = new ArrayList<>();

            // DeepL批量翻译API返回的结果顺序应该与输入顺序一致
            // 但为了确保，我们按照translations数组的顺序添加结果
            for (int i = 0; i < translations.size(); i++) {
                com.google.gson.JsonObject translation = translations.get(i).getAsJsonObject();
                String translatedText = translation.get("text").getAsString();
                results.add(translatedText);
            }

            // 验证结果数量是否匹配
            if (results.size() != texts.size()) {
                throw new Exception("批量翻译结果数量不匹配：期望 " + texts.size() + " 个，实际 " + results.size() + " 个");
            }

            // 优化：批量翻译成功时输出一次日志
            if (texts.size() > 1) {
                System.out.println("✅ 批量翻译完成，共 " + results.size() + " 个结果");
            }

            return results;
        } else {
            // 读取错误响应
            java.io.BufferedReader errorReader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getErrorStream(), "UTF-8"));
            StringBuilder errorResponse = new StringBuilder();
            String errorLine;
            while ((errorLine = errorReader.readLine()) != null) {
                errorResponse.append(errorLine);
            }
            errorReader.close();

            throw new Exception("DeepL API错误码: " + responseCode + ", 错误信息: " + errorResponse.toString());
        }
    }

    private static String translateWithDeepL(String text, String from, String to) throws Exception {
        // 从配置类获取API密钥
        if (!TranslationConfig.isDeepLConfigured()) {
            throw new Exception("请先在TranslationConfig中设置DeepL API密钥");
        }

        String apiKey = TranslationConfig.DEEPL_API_KEY;

        // 语言代码转换
        String sourceLang = from.equals("en") ? "EN" : from.toUpperCase();
        String targetLang = to.equals("zh") ? "ZH" : to.toUpperCase();

        // 使用DeepL Pro API端点
        String url = "https://api.deepl-pro.com/v2/translate";
        String postData = "auth_key=" + apiKey +
                "&text=" + java.net.URLEncoder.encode(text, "UTF-8") +
                "&source_lang=" + sourceLang +
                "&target_lang=" + targetLang;

        java.net.URL urlObj = new java.net.URI(url).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) urlObj.openConnection();
        connection.setRequestMethod("POST");
        connection.setRequestProperty("Content-Type", "application/x-www-form-urlencoded");
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(8000); // 优化：减少超时时间到8秒
        connection.setReadTimeout(10000); // 优化：读取超时10秒
        connection.setDoOutput(true);

        // 优化：减少日志输出以提高速度（仅在需要时输出）
        // System.out.println("  DeepL API URL: " + url);
        // System.out.println("  DeepL API Key: " + apiKey.substring(0, Math.min(10, apiKey.length())) + "...");
        // System.out.println("  Source Lang: " + sourceLang + ", Target Lang: " + targetLang);

        // 发送POST数据
        try (java.io.OutputStream os = connection.getOutputStream()) {
            byte[] input = postData.getBytes("UTF-8");
            os.write(input, 0, input.length);
        }

        int responseCode = connection.getResponseCode();
        if (responseCode == 200) {
            java.io.BufferedReader reader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getInputStream(), "UTF-8"));
            StringBuilder response = new StringBuilder();
            String line;
            while ((line = reader.readLine()) != null) {
                response.append(line);
            }
            reader.close();

            // 解析DeepL JSON响应
            com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(response.toString()).getAsJsonObject();
            com.google.gson.JsonArray translations = jsonResponse.getAsJsonArray("translations");
            if (translations.size() > 0) {
                com.google.gson.JsonObject translation = translations.get(0).getAsJsonObject();
                String translatedText = translation.get("text").getAsString();
                return translatedText;
            }
        } else {
            // 读取错误响应
            java.io.BufferedReader errorReader = new java.io.BufferedReader(
                    new java.io.InputStreamReader(connection.getErrorStream(), "UTF-8"));
            StringBuilder errorResponse = new StringBuilder();
            String errorLine;
            while ((errorLine = errorReader.readLine()) != null) {
                errorResponse.append(errorLine);
            }
            errorReader.close();

            throw new Exception("DeepL API错误码: " + responseCode + ", 错误信息: " + errorResponse.toString());
        }

        return text;
    }


    /**
     * LibreTranslate翻译API - 已禁用
     */
    /* DISABLED
    private static String translateWithLibreTranslate(String text, String from, String to) throws Exception {
        String[] endpoints = {
            "https://libretranslate.de/translate",
            "https://translate.argosopentech.com/translate",
            "https://translate.fortytwo-it.com/translate"
        };

        Exception lastException = null;

        for (String endpoint : endpoints) {
            try {
                String encodedText = java.net.URLEncoder.encode(text, java.nio.charset.StandardCharsets.UTF_8);
                String postData = "q=" + encodedText + "&source=" + from + "&target=" + to + "&format=text";

                java.net.URL url = new java.net.URL(endpoint);
                java.net.HttpURLConnection connection = (java.net.HttpURLConnection) url.openConnection();
                connection.setRequestMethod("POST");
                connection.setRequestProperty("Content-Type", "application/x-www-form-urlencoded");
                connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
                connection.setDoOutput(true);
                connection.setConnectTimeout(30000);  // 增加到30秒
                connection.setReadTimeout(30000);      // 增加到30秒

                // 发送POST数据
                java.io.DataOutputStream wr = new java.io.DataOutputStream(connection.getOutputStream());
                wr.writeBytes(postData);
                wr.flush();
                wr.close();

                // 读取响应
                java.io.BufferedReader reader = new java.io.BufferedReader(
                        new java.io.InputStreamReader(connection.getInputStream(), java.nio.charset.StandardCharsets.UTF_8));

                StringBuilder response = new StringBuilder();
                String line;
                while ((line = reader.readLine()) != null) {
                    response.append(line);
                }
                reader.close();

                // 检查响应是否为空
                String responseStr = response.toString().trim();
                if (responseStr.isEmpty()) {
                    throw new Exception("LibreTranslate返回空响应");
                }

                // 调试：打印响应内容
                System.out.println("  📥 LibreTranslate响应: " + responseStr.substring(0, Math.min(100, responseStr.length())));

                // 使用lenient模式解析JSON（允许格式不严格的JSON）
                com.google.gson.JsonParser parser = new com.google.gson.JsonParser();
                com.google.gson.JsonElement jsonElement = parser.parse(responseStr);

                if (!jsonElement.isJsonObject()) {
                    throw new Exception("LibreTranslate返回的不是JSON对象");
                }

                com.google.gson.JsonObject jsonResponse = jsonElement.getAsJsonObject();

                if (!jsonResponse.has("translatedText")) {
                    throw new Exception("LibreTranslate响应中没有translatedText字段");
                }

                String translatedText = jsonResponse.get("translatedText").getAsString();

                connection.disconnect();
                return translatedText;
            } catch (java.net.SocketTimeoutException e) {
                lastException = e;
                System.out.println("  ⚠️ LibreTranslate超时: " + endpoint);
                continue;
            } catch (java.net.ConnectException e) {
                lastException = e;
                System.out.println("  ⚠️ LibreTranslate连接失败: " + endpoint);
                continue;
            } catch (java.net.UnknownHostException e) {
                lastException = e;
                System.out.println("  ⚠️ LibreTranslate域名无法解析: " + endpoint);
                continue;
            } catch (com.google.gson.JsonSyntaxException e) {
                lastException = e;
                System.out.println("  ⚠️ LibreTranslate JSON解析错误: " + endpoint);
                System.out.println("     错误详情: " + e.getMessage());
                continue;
            } catch (Exception e) {
                lastException = e;
                System.out.println("  ⚠️ LibreTranslate错误: " + e.getClass().getSimpleName() + " - " + e.getMessage());
                continue;
            }
        }

        throw lastException != null ? lastException : new Exception("所有LibreTranslate端点都失败");
    }
    END DISABLED */

    // ============================================================
    // 当前使用的翻译API
    // ============================================================

    /**
     * MyMemory翻译API（改进版）
     */
    private static String translateWithMyMemory(String text, String from, String to) throws Exception {
        String encodedText = java.net.URLEncoder.encode(text, java.nio.charset.StandardCharsets.UTF_8);
        String urlStr = "https://api.mymemory.translated.net/get?q=" + encodedText +
                "&langpair=" + from + "|" + to;

        java.net.URL url = new java.net.URI(urlStr).toURL();
        java.net.HttpURLConnection connection = (java.net.HttpURLConnection) url.openConnection();
        connection.setRequestMethod("GET");
        connection.setRequestProperty("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36");
        connection.setConnectTimeout(30000);  // 增加到30秒
        connection.setReadTimeout(30000);      // 增加到30秒

        // 检查响应码
        int responseCode = connection.getResponseCode();
        if (responseCode == 429) {
            // 请求过多，等待后重试
            System.out.println("⚠️ 请求过多，等待5秒后重试...");
            // 优化：减少重试延迟时间（从5秒减少到2秒）
            Thread.sleep(2000);
            return translateWithMyMemory(text, from, to); // 递归重试
        } else if (responseCode != 200) {
            throw new Exception("HTTP错误码: " + responseCode);
        }

        java.io.BufferedReader reader = new java.io.BufferedReader(
                new java.io.InputStreamReader(connection.getInputStream(), java.nio.charset.StandardCharsets.UTF_8));

        StringBuilder response = new StringBuilder();
        String line;
        while ((line = reader.readLine()) != null) {
            response.append(line);
        }
        reader.close();
        connection.disconnect();

        // 检查响应是否为空
        String responseStr = response.toString().trim();
        if (responseStr.isEmpty()) {
            throw new Exception("MyMemory返回空响应");
        }

        // 解析JSON响应
        com.google.gson.JsonObject jsonResponse = com.google.gson.JsonParser.parseString(responseStr).getAsJsonObject();

        // 检查是否有responseData字段
        if (!jsonResponse.has("responseData")) {
            throw new Exception("MyMemory响应中没有responseData字段");
        }

        com.google.gson.JsonObject responseData = jsonResponse.getAsJsonObject("responseData");

        // 检查是否有translatedText字段
        if (!responseData.has("translatedText")) {
            throw new Exception("MyMemory响应中没有translatedText字段");
        }

        String translatedText = responseData.get("translatedText").getAsString();

        // 检查翻译结果是否为空
        if (translatedText.isEmpty()) {
            throw new Exception("MyMemory返回空翻译");
        }

        return decodeUnicode(translatedText);
    }

    /**
     * 解码Unicode字符
     */
    private static String decodeUnicode(String text) {
        StringBuilder result = new StringBuilder();
        int i = 0;
        while (i < text.length()) {
            if (text.charAt(i) == '\\' && i + 1 < text.length() && text.charAt(i + 1) == 'u') {
                try {
                    String unicode = text.substring(i + 2, i + 6);
                    int codePoint = Integer.parseInt(unicode, 16);
                    result.append((char) codePoint);
                    i += 6;
                } catch (Exception e) {
                    result.append(text.charAt(i));
                    i++;
                }
            } else {
                result.append(text.charAt(i));
                i++;
            }
        }
        return result.toString();
    }

    /**
     * 拆分包含数字序号的文本为独立的列表项（如1. 2. 3. 4.）
     * 只匹配真正的序号，忽略句子内部的编号如(1) (2) (3)
     */
    private static List<String> splitNumberedItems(String text) {
        List<String> items = new ArrayList<>();

        // 智能检测：区分真正的序号和句子内部的编号
        // 策略：查找以数字序号开头且以句号结尾的完整句子

        // 先尝试按换行符分割
        String[] lines = text.split("\\n");
        if (lines.length > 1) {
            // 多行文本，检查每行是否以数字序号开头
            List<String> numberedLines = new ArrayList<>();
            for (String line : lines) {
                line = line.trim();
                if (isNumberedItem(line)) {
                    numberedLines.add(line);
                }
            }

            if (numberedLines.size() > 1) {
                items.addAll(numberedLines);
                return items;
            }
        }

        // 单行文本，需要智能分析
        // 查找模式：数字序号 + 空格 + 大写字母开头 + ... + 句号
        // 但要排除句子内部的编号如(1) (2) (3)

        // 使用更简单的方法：查找以数字序号开头且以句号结尾的句子
        java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                "\\b(\\d+[.)]\\s+[A-Z][^.]*\\.)"
        );
        java.util.regex.Matcher matcher = pattern.matcher(text);

        List<String> foundItems = new ArrayList<>();
        while (matcher.find()) {
            String item = matcher.group(1).trim();
            foundItems.add(item);
        }

        if (foundItems.size() > 1) {
            // 找到多个完整的序号句子
            items.addAll(foundItems);
        } else {
            // 没有找到多个序号句子，返回原文本
            items.add(text);
        }

        return items;
    }

    /**
     * 拆分包含多个"•"的文本为独立的列表项
     */
    private static List<String> splitBulletItems(String text) {
        List<String> items = new ArrayList<>();

        // 检查是否包含"•"
        if (!text.contains("•")) {
            items.add(text);
            return items;
        }

        // 找到所有"•"的位置
        List<Integer> bulletPositions = new ArrayList<>();
        for (int i = 0; i < text.length(); i++) {
            if (text.charAt(i) == '•') {
                bulletPositions.add(i);
            }
        }

        // 根据"•"的位置拆分文本
        for (int i = 0; i < bulletPositions.size(); i++) {
            int startPos = bulletPositions.get(i);
            int endPos = (i + 1 < bulletPositions.size()) ? bulletPositions.get(i + 1) : text.length();

            String item = text.substring(startPos, endPos).trim();
            if (!item.isEmpty() && !item.equals("•")) {
                items.add(item);
            }
        }

        return items;
    }

    /**
     * 拆分以短横线列表符（–/—/−/-）开头的分段项：
     * - 多行时：将每一行视为独立段落，其中以 "– " / "— " / "- " 开头的行作为新段落
     * - 单行时：兼容 PDF 抽取把换行压成空格的情况：按多个「空白 + dash + 空白」拆成多段
     */
    private static List<String> splitDashItems(String text) {
        if (text == null || text.isEmpty()) {
            return java.util.Collections.emptyList();
        }

        String t = text.replace("\r\n", "\n").replace("\r", "\n");
        List<String> items = new ArrayList<>();

        // 多行：逐行拆分（你的示例 "Eigen function\n– Proof..." 会走这里）
        if (t.contains("\n")) {
            String[] lines = t.split("\\n");
            for (String line : lines) {
                String one = line == null ? "" : line.trim();
                if (one.isEmpty()) continue;
                items.add(one);
            }
            return items.size() > 1 ? items : java.util.Collections.singletonList(text);
        }

        // 单行：按多个「空白 + dash + 空白」拆分（dash=–/—/−/-），并要求后续看起来像条目/新句子开头以减少误拆
        // 例如："... Properties of CTFT – Linearity ... – System ..."（原本是换行的子要点）
        java.util.regex.Pattern p = java.util.regex.Pattern.compile(
                "\\s([\\u2013\\u2014\\u2212-])\\s+(?=[A-Za-z(])"
        );
        java.util.regex.Matcher m = p.matcher(t);
        int last = 0;
        boolean any = false;
        while (m.find()) {
            int dashPos = m.start(1);
            String left = t.substring(last, dashPos).trim();
            if (!left.isEmpty()) {
                items.add(left);
            }
            last = dashPos;
            any = true;
        }
        if (any) {
            String tail = t.substring(last).trim();
            if (!tail.isEmpty()) {
                items.add(tail);
            }
            return items.size() > 1 ? items : java.util.Collections.singletonList(text);
        }

        return java.util.Collections.singletonList(text);
    }

    /**
     * 拆分包含"分行符变n"的文本为独立行
     * PDF复制粘贴时换行符(\n)会变成字母"n"，导致多行被合并成一行，如：
     * "nOOP Recap nWhat is a good design nSOLID Principles nLoosen coupling using composition"
     * 应拆分为四行并去除每行开头的"n"
     */
    private static List<String> splitCorruptedNewlineItems(String text) {
        List<String> items = new ArrayList<>();
        if (text == null || text.isEmpty()) {
            return items;
        }
        // 按 " n" 拆分（空格+n 表示被合并的换行，后面通常跟大写字母或数字）
        String[] parts = text.split(" (?=n[A-Z0-9])");
        for (String part : parts) {
            part = part.trim();
            if (part.isEmpty()) continue;
            // 去除行首的"n"（分行符的残留）：n后跟大写字母或数字
            if (part.length() > 1 && part.startsWith("n") &&
                    (Character.isUpperCase(part.charAt(1)) || Character.isDigit(part.charAt(1)))) {
                part = part.substring(1).trim();
            } else if (part.startsWith("n ") && part.length() > 2) {
                part = part.substring(2).trim();
            }
            if (!part.isEmpty()) {
                items.add(part);
            }
        }
        return items.isEmpty() ? java.util.Collections.singletonList(text) : items;
    }

    /**
     * 拆分包含特殊符号的文本为独立的段落
     * 支持：
     * 1. U+F06C 字符（特殊分段符号）
     * 2. "■" 字符（实心方块，直接的分段符号）
     * 3. "n" 字符（方框符号"■"的复制粘贴结果，作为分段符号）
     */
    private static List<String> splitSpecialSymbolItems(String text) {
        List<String> items = new ArrayList<>();

        // 检查是否包含任何分段符号
        char specialChar = (char) 0xF06C;
        String specialCharStr = String.valueOf(specialChar);
        boolean hasSpecialChar = text.contains(specialCharStr);
        boolean hasBoxChar = text.contains("■");
        boolean hasBoxCharAsN = detectBoxCharAsN(text);

        if (!hasSpecialChar && !hasBoxChar && !hasBoxCharAsN) {
            items.add(text);
            return items;
        }

        // 找到所有分段符号的位置
        List<Integer> symbolPositions = new ArrayList<>();
        for (int i = 0; i < text.length(); i++) {
            char c = text.charAt(i);
            // 检测U+F06C字符
            if (c == specialChar) {
                symbolPositions.add(i);
            }
            // 检测"■"字符
            else if (c == '■') {
                symbolPositions.add(i);
            }
            // 检测"n"作为方框符号（分段符号）
            // 判断条件：n在行首或前面是空格，后面跟空格和大写字母/数字（新段落的开始）
            else if (c == 'n' && isBoxCharAsN(text, i)) {
                symbolPositions.add(i);
            }
        }

        // 如果没有找到分段符号，返回原文本
        if (symbolPositions.isEmpty()) {
            items.add(text);
            return items;
        }

        // 根据分段符号的位置拆分文本
        for (int i = 0; i < symbolPositions.size(); i++) {
            int startPos = symbolPositions.get(i);
            int endPos = (i + 1 < symbolPositions.size()) ? symbolPositions.get(i + 1) : text.length();

            String item = text.substring(startPos, endPos).trim();
            // 移除分段符号，只保留内容
            item = item.replace(specialCharStr, "").trim();
            item = item.replace("■", "").trim();
            // 移除"n"分段符号（只移除作为分段符号的"n"，即行首的"n "或"n"后直接跟大写字母/数字）
            if (item.startsWith("n ") && (item.length() == 2 || Character.isUpperCase(item.charAt(2)) || Character.isDigit(item.charAt(2)))) {
                item = item.substring(2).trim();
            } else if (item.startsWith("n") && item.length() > 1 && (Character.isUpperCase(item.charAt(1)) || Character.isDigit(item.charAt(1)))) {
                item = item.substring(1).trim();
            }
            if (!item.isEmpty()) {
                items.add(item);
            }
        }

        return items;
    }

    /**
     * 检测文本中是否包含作为分段符号的"n"（方框符号的复制结果）
     */
    private static boolean detectBoxCharAsN(String text) {
        // 检测模式：行首的"n "后面跟大写字母或数字（新段落）
        // 或者单独的"n"后面直接跟大写字母或数字
        // 或者"n"前面是空格/换行，后面是空格+大写字母/数字
        java.util.regex.Pattern pattern = java.util.regex.Pattern.compile(
                "(^|\\s)n\\s+[A-Z0-9]|^n[A-Z0-9]|\\s+n\\s+[A-Z0-9]"
        );
        return pattern.matcher(text).find();
    }

    /**
     * 判断指定位置的"n"是否是作为分段符号的方框符号
     */
    private static boolean isBoxCharAsN(String text, int pos) {
        // 检查"n"是否在行首（前面是文本开头、空格或换行）
        boolean isAtLineStart = (pos == 0) ||
                (pos > 0 && (text.charAt(pos - 1) == ' ' || text.charAt(pos - 1) == '\n'));

        if (!isAtLineStart) {
            return false;
        }

        // 检查"n"后面是否跟着空格和大写字母/数字（新段落开始）
        if (pos + 1 < text.length()) {
            char nextChar = text.charAt(pos + 1);
            // "n"后面直接跟大写字母或数字
            if (Character.isUpperCase(nextChar) || Character.isDigit(nextChar)) {
                return true;
            }
            // "n"后面跟空格，然后是大写字母或数字
            if (nextChar == ' ' && pos + 2 < text.length()) {
                char afterSpace = text.charAt(pos + 2);
                if (Character.isUpperCase(afterSpace) || Character.isDigit(afterSpace)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * 计算每个特殊符号段落的Y坐标
     */
    private static float calculateSpecialSymbolItemY(List<CoordinateTextStripper.TextItem> group,
                                                     int itemIndex, float pageHeight, boolean isMultiline,
                                                     int totalItems, boolean isReversedCoordinate) {
        // 计算组的底部Y坐标
        float groupBottomY;
        if (isReversedCoordinate) {
            // 反向坐标系：Y值小在上，Y值大在下
            groupBottomY = 0;
            for (CoordinateTextStripper.TextItem item : group) {
                groupBottomY = Math.max(groupBottomY, item.y);
            }
        } else {
            // 标准PDFBox坐标系：Y值大在上，Y值小在下
            groupBottomY = Float.MAX_VALUE;
            for (CoordinateTextStripper.TextItem item : group) {
                groupBottomY = Math.min(groupBottomY, item.y);
            }
        }

        // 转换为从顶部开始的坐标
        float englishBottomY;
        if (isReversedCoordinate) {
            // 反向坐标系：Y值本身就是从顶部开始的距离
            englishBottomY = groupBottomY;
        } else {
            // 标准PDFBox坐标系：需要转换
            englishBottomY = pageHeight - groupBottomY;
        }

        // 每个段落向下偏移，译文放在原文下方
        float baseSpacing = 16; // 基础间距（译文在原文下方），增加4个单位（从12改为16）
        float itemSpacing = 5; // 每个段落之间的额外间距
        float translationY = englishBottomY + baseSpacing + itemSpacing * itemIndex;

        // 确保译文不会超出页面底部
        if (translationY > pageHeight) {
            translationY = pageHeight - 10; // 留10像素边距
        }

        return translationY;
    }

    /**
     * 计算每个数字序号项的Y坐标
     */
    private static float calculateNumberedItemY(List<CoordinateTextStripper.TextItem> group,
                                                int itemIndex, float pageHeight, boolean isMultiline) {
        // 计算组的顶部Y坐标（假设是反向坐标系，因为这是最常见的）
        float groupTopY = Float.MAX_VALUE;
        for (CoordinateTextStripper.TextItem item : group) {
            groupTopY = Math.min(groupTopY, item.y);
        }

        // 转换为从顶部开始的坐标（假设反向坐标系）
        float englishTopY = groupTopY;

        // 每个列表项向下偏移，译文放在原文下方
        float baseSpacing = 16; // 基础间距（译文在原文下方），增加4个单位（从12改为16）
        float itemSpacing = 5; // 每个列表项之间的额外间距
        float translationY = englishTopY + baseSpacing + itemSpacing * itemIndex;

        // 确保译文不会超出页面底部
        if (translationY > pageHeight) {
            translationY = pageHeight - 10; // 留10像素边距
        }

        return translationY;
    }

    /**
     * 计算拆分项在group中对应的X坐标
     * @param group 文本组
     * @param fullText 完整的原始文本
     * @param itemText 拆分项的文本（去除首尾空格）
     * @param itemIndex 拆分项的索引
     * @param allItems 所有拆分项的列表
     * @return 拆分项对应的X坐标
     */
    private static float calculateItemX(List<CoordinateTextStripper.TextItem> group,
                                        String fullText, String itemText, int itemIndex, List<String> allItems) {
        // 清理itemText，去除首尾空格
        String cleanItemText = itemText.trim();

        // 找到拆分项在完整文本中的起始位置
        // 先找到前面所有项的位置，确定搜索起点
        int searchStart = 0;
        for (int i = 0; i < itemIndex; i++) {
            String prevItem = allItems.get(i).trim();
            int pos = fullText.indexOf(prevItem, searchStart);
            if (pos >= 0) {
                searchStart = pos + prevItem.length();
            }
        }

        // 在完整文本中查找当前项的位置
        int itemStartPos = fullText.indexOf(cleanItemText, searchStart);
        if (itemStartPos < 0) {
            // 如果找不到精确匹配，尝试查找部分匹配（去除序号等）
            String itemWithoutPrefix = cleanItemText.replaceFirst("^\\d+[.)]\\s*", "")
                    .replaceFirst("^[•]\\s*", "")
                    .replaceFirst("^[—–−-]\\s+", "")
                    .trim();
            if (!itemWithoutPrefix.isEmpty()) {
                itemStartPos = fullText.indexOf(itemWithoutPrefix, searchStart);
            }
        }

        if (itemStartPos < 0) {
            // 如果还是找不到，使用groupX作为默认值
            float groupX = Float.MAX_VALUE;
            for (CoordinateTextStripper.TextItem item : group) {
                groupX = Math.min(groupX, item.x);
            }
            return groupX;
        }

        // 计算itemStartPos对应的字符位置在group中的位置
        // 重建group的文本，找到对应的TextItem
        int currentPos = 0;
        for (CoordinateTextStripper.TextItem item : group) {
            String itemTextWithSpace = item.text + " ";
            int itemLength = itemTextWithSpace.length();

            // 检查itemStartPos是否在当前TextItem的范围内
            if (currentPos <= itemStartPos && itemStartPos < currentPos + itemLength) {
                // 找到了对应的TextItem，使用它的X坐标
                return item.x;
            }
            currentPos += itemLength;
        }

        // 如果找不到，使用groupX作为默认值
        float groupX = Float.MAX_VALUE;
        for (CoordinateTextStripper.TextItem item : group) {
            groupX = Math.min(groupX, item.x);
        }
        return groupX;
    }

    /**
     * 计算拆分项在 group 中对应的「从顶部开始」Y 坐标，用于把译文放在该项原文行下方。
     * 逻辑与 {@link #calculateItemX} 类似：先找拆分项在 fullText 中的起始字符位置，再映射到对应的 TextItem.y。
     */
    private static float calculateItemYFromTop(List<CoordinateTextStripper.TextItem> group,
                                               String fullText, String itemText, int itemIndex, List<String> allItems,
                                               float pageHeight, boolean isReversedCoordinate) {
        if (group == null || group.isEmpty()) {
            return 16f;
        }
        String cleanItemText = itemText == null ? "" : itemText.trim();

        // 用「字符区间 -> TextItem 范围」来估计该子条目的行块底部位置：
        // 这样即使该条目跨多行/被拆成多个 TextItem，也能把译文稳定放到该条目自身下方。
        int itemStart = findItemStartInFullText(fullText, allItems, itemIndex);
        int itemEnd = findItemEndInFullText(fullText, allItems, itemIndex, itemStart);

        if (itemStart >= 0 && itemEnd > itemStart) {
            float bottomY = findGroupBottomYForCharRange(group, itemStart, itemEnd, isReversedCoordinate);
            if (bottomY >= 0) {
                float englishBottomFromTop = isReversedCoordinate ? bottomY : (pageHeight - bottomY);
                float y = englishBottomFromTop + 16f; // 放在该条目行块下方
                if (y > pageHeight) y = pageHeight - 10;
                return y;
            }
        }

        // 兜底：用核心文本的第一个关键词在 TextItem 里反查所在行的 y（对 PDF 抽取空格/破折号变形更稳）
        String itemCore = cleanItemText.replaceFirst("^\\d+[.)]\\s*", "")
                .replaceFirst("^[•]\\s*", "")
                .replaceFirst("^[—–−-]\\s+", "")
                .trim();
        String anchor = extractFirstAnchorWord(itemCore.isEmpty() ? cleanItemText : itemCore);
        if (anchor != null && !anchor.isEmpty()) {
            int hit = findTextItemIndexContainingWord(group, anchor, 0);
            if (hit >= 0) {
                CoordinateTextStripper.TextItem it = group.get(hit);
                float englishTopY = isReversedCoordinate ? it.y : (pageHeight - it.y);
                float y = englishTopY + 16f;
                if (y > pageHeight) y = pageHeight - 10;
                return y;
            }
        }

        // 最终回退：按组顶部等距堆叠（不崩即可）
        return calculateBulletItemY(group, itemIndex, pageHeight, false);
    }

    /**
     * 根据 allItems 的顺序，在 fullText 中找到 itemIndex 对应子条目的起始位置。
     * 优先用去掉列表符号后的核心文本，以适配 dash 变体与空格差异。
     */
    private static int findItemStartInFullText(String fullText, List<String> allItems, int itemIndex) {
        if (fullText == null || allItems == null || itemIndex < 0 || itemIndex >= allItems.size()) return -1;
        int searchStart = 0;
        for (int i = 0; i < itemIndex; i++) {
            String prev = allItems.get(i) == null ? "" : allItems.get(i).trim();
            if (prev.isEmpty()) continue;
            String prevCore = prev.replaceFirst("^\\d+[.)]\\s*", "")
                    .replaceFirst("^[•]\\s*", "")
                    .replaceFirst("^[—–−-]\\s+", "")
                    .trim();
            String token = !prevCore.isEmpty() ? prevCore : prev;
            int pos = fullText.indexOf(token, searchStart);
            if (pos >= 0) searchStart = pos + token.length();
        }
        String cur = allItems.get(itemIndex) == null ? "" : allItems.get(itemIndex).trim();
        if (cur.isEmpty()) return -1;
        String curCore = cur.replaceFirst("^\\d+[.)]\\s*", "")
                .replaceFirst("^[•]\\s*", "")
                .replaceFirst("^[—–−-]\\s+", "")
                .trim();
        int pos = -1;
        if (!curCore.isEmpty()) pos = fullText.indexOf(curCore, searchStart);
        if (pos < 0) pos = fullText.indexOf(cur, searchStart);
        return pos;
    }

    /** itemEnd = 下一条起始位置；若找不到则用 fullText.length()。 */
    private static int findItemEndInFullText(String fullText, List<String> allItems, int itemIndex, int itemStart) {
        if (fullText == null || allItems == null) return -1;
        if (itemStart < 0) return -1;
        if (itemIndex + 1 >= allItems.size()) return fullText.length();
        int nextStart = findItemStartInFullText(fullText, allItems, itemIndex + 1);
        if (nextStart > itemStart) return nextStart;
        return fullText.length();
    }

    /**
     * 将 group 的 TextItem 串联为「item.text + ' '」的字符流，并对齐到指定字符区间，
     * 返回该区间覆盖到的 TextItem 的“底部 y”（标准坐标系取最小 y；反向坐标系取最大 y）。
     */
    private static float findGroupBottomYForCharRange(List<CoordinateTextStripper.TextItem> group,
                                                      int startChar, int endChar,
                                                      boolean isReversedCoordinate) {
        if (group == null || group.isEmpty()) return -1f;
        if (startChar < 0 || endChar <= startChar) return -1f;

        int pos = 0;
        boolean hitAny = false;
        float bottomY = isReversedCoordinate ? Float.NEGATIVE_INFINITY : Float.POSITIVE_INFINITY;
        for (CoordinateTextStripper.TextItem it : group) {
            String s = (it != null && it.text != null) ? it.text : "";
            String withSpace = s + " ";
            int len = withSpace.length();
            int segStart = pos;
            int segEnd = pos + len;
            // 区间有交集
            if (segEnd > startChar && segStart < endChar) {
                hitAny = true;
                if (isReversedCoordinate) bottomY = Math.max(bottomY, it.y);
                else bottomY = Math.min(bottomY, it.y);
            }
            pos = segEnd;
            if (pos >= endChar) break;
        }
        return hitAny ? bottomY : -1f;
    }

    /** 提取用于定位的首个英文关键词（长度>=2），如 "Linearity" / "System"。 */
    private static String extractFirstAnchorWord(String s) {
        if (s == null) return "";
        String t = s.trim();
        if (t.isEmpty()) return "";
        java.util.regex.Matcher m = java.util.regex.Pattern.compile("[A-Za-z]{2,}").matcher(t);
        if (m.find()) return m.group();
        return "";
    }

    /** 在 group 中寻找包含 anchor（不区分大小写）的第一个 TextItem 索引。 */
    private static int findTextItemIndexContainingWord(List<CoordinateTextStripper.TextItem> group, String anchor, int startIdx) {
        if (group == null || group.isEmpty()) return -1;
        if (anchor == null || anchor.isEmpty()) return -1;
        String a = anchor.toLowerCase(Locale.ROOT);
        int s = Math.max(0, startIdx);
        for (int i = s; i < group.size(); i++) {
            CoordinateTextStripper.TextItem it = group.get(i);
            String tx = it != null && it.text != null ? it.text : "";
            if (tx.isEmpty()) continue;
            if (tx.toLowerCase(Locale.ROOT).contains(a)) return i;
        }
        return -1;
    }

    /**
     * 计算每个列表项的Y坐标
     */
    private static float calculateBulletItemY(List<CoordinateTextStripper.TextItem> group,
                                              int itemIndex, float pageHeight, boolean isMultiline) {
        // 计算组的顶部Y坐标（假设是反向坐标系，因为这是最常见的）
        float groupTopY = Float.MAX_VALUE;
        for (CoordinateTextStripper.TextItem item : group) {
            groupTopY = Math.min(groupTopY, item.y);
        }

        // 转换为从顶部开始的坐标（假设反向坐标系）
        float englishTopY = groupTopY;

        // 每个列表项向下偏移，译文放在原文下方
        float baseSpacing = 16; // 基础间距（译文在原文下方），增加4个单位（从12改为16）
        float itemSpacing = 5; // 每个列表项之间的额外间距
        float translationY = englishTopY + baseSpacing + itemSpacing * itemIndex;

        // 确保译文不会超出页面底部
        if (translationY > pageHeight) {
            translationY = pageHeight - 10; // 留10像素边距
        }

        return translationY;
    }

    /**
     * 创建可编辑文本框
     * @param y 从顶部开始的Y坐标（需要转换为PDFBox坐标系）
     */
    private static void createEditableTextBox(PDPage page, String translated,
                                              float x, float y, int groupIndex, float pageHeight) throws Exception {

        // 计算文本框大小
        float textBoxWidth = Math.max(200, translated.length() * 6 + 20); // 根据文本长度计算宽度
        float textBoxHeight = 30; // 固定高度

        // 将Y坐标从"从顶部开始"转换为PDFBox坐标系（从底部开始）
        // PDFBox坐标系：Y从底部开始，Y值越大越靠上
        // PDRectangle的Y坐标是文本框左下角的位置
        // 转换公式：pdfBoxY = pageHeight - y - textBoxHeight
        float pdfBoxY = pageHeight - y - textBoxHeight;

        // 使用PDAnnotationText创建文本注释（PDFBox 2.0.30兼容）
        PDAnnotationText textBox = new PDAnnotationText();

        // 设置文本框位置和大小
        PDRectangle rect = new PDRectangle(x, pdfBoxY, textBoxWidth, textBoxHeight);
        textBox.setRectangle(rect);

        // 设置文本框内容
        textBox.setContents(translated);

        // 设置文本框属性
        textBox.setOpen(true); // 默认打开状态

        // 注意：PDAnnotationText没有setTitle和setAnnotationType方法
        // 这些属性在PDFBox 2.0.30中通过其他方式设置

        // 添加到页面
        page.getAnnotations().add(textBox);

        System.out.println("  📦 创建文本框: x=" + x + ", y（从顶部）=" + y +
                ", y（PDFBox坐标系）=" + pdfBoxY +
                ", 宽度=" + textBoxWidth + ", 高度=" + textBoxHeight);
    }

    /**
     * 绘制翻译文本（简单版本，不支持重叠检测，用于列表项等）
     * @param y 从顶部开始的Y坐标（需要转换为PDFBox坐标系）
     */
    private static void drawTranslationSimple(PDPageContentStream contentStream, PDType0Font chineseFont,
                                              float x, float y, String translated, float pageWidth, float pageHeight) throws Exception {
        // 将Y坐标从"从顶部开始"转换为PDFBox坐标系（从底部开始）
        float pdfBoxY = pageHeight - y;

        // 处理特殊字符和换行符
        String safeText = translated.replace("•", "-")
                .replace("→", "->")
                .replace("\n", " ")
                .replace("\r", " ")
                .trim();

        // 过滤掉字体不支持的字符
        StringBuilder filteredText = new StringBuilder();
        for (int i = 0; i < safeText.length(); i++) {
            char c = safeText.charAt(i);
            if (isSupportedChar(c)) {
                filteredText.append(c);
            } else {
                filteredText.append(' ');
            }
        }
        safeText = filteredText.toString().replaceAll("\\s+", " ").trim();

        float rightMargin = 20.0f;
        float fontSize = TRANSLATION_ZH_FONT_SIZE_PT;
        float lineHeight = TRANSLATION_ZH_LINE_HEIGHT_PT;
        float charWidth = fontSize * 1.1f;
        float availableWidth = pageWidth - x - rightMargin;
        int charsPerLine = Math.max(1, (int) (availableWidth / charWidth));

        // 分割文本为多行
        List<String> lines = wrapText(safeText, charsPerLine);

        // 绘制每一行
        float currentY = pdfBoxY;
        for (int i = 0; i < lines.size(); i++) {
            String line = lines.get(i);
            contentStream.setNonStrokingColor(java.awt.Color.BLACK);
            contentStream.beginText();
            contentStream.setFont(chineseFont, fontSize);
            contentStream.newLineAtOffset(x, currentY);
            contentStream.showText(line);
            contentStream.endText();
            currentY -= lineHeight;
        }
    }

    /**
     * 绘制翻译文本（支持自动换行）
     * @param y 从顶部开始的Y坐标（需要转换为PDFBox坐标系）
     * @param textGroups 所有文本组
     * @param currentGroupIndex 当前文本组的索引
     * @param groupY 当前文本组的顶部Y坐标（PDFBox坐标系）
     * @param groupBottomY 当前文本组的底部Y坐标（PDFBox坐标系）
     * @param isReversedCoordinate 是否反向坐标系
     * @param isOCRMode 是否OCR模式
     */
    private static void drawTranslation(PDPageContentStream contentStream, PDType0Font chineseFont,
                                        float x, float y, String translated, float pageWidth, float pageHeight,
                                        List<List<CoordinateTextStripper.TextItem>> textGroups, int currentGroupIndex,
                                        float groupY, float groupBottomY, boolean isReversedCoordinate, boolean isOCRMode) throws Exception {
        // 将Y坐标从"从顶部开始"转换为PDFBox坐标系（从底部开始）
        // PDFBox坐标系：Y从底部开始，Y值越大越靠上
        // 转换公式：pdfBoxY = pageHeight - y
        float pdfBoxY = pageHeight - y;

        // 处理特殊字符和换行符
        // 移除换行符，因为PDFBox的showText不支持换行符
        // 替换或移除不支持的字符
        String safeText = translated.replace("•", "-")
                .replace("→", "->")
                .replace("\n", " ")
                .replace("\r", " ")
                .trim();

        // 过滤掉字体不支持的字符（如U+F06C等特殊符号）
        // 只保留中文字符、英文字母、数字、常用标点符号和空格
        StringBuilder filteredText = new StringBuilder();
        for (int i = 0; i < safeText.length(); i++) {
            char c = safeText.charAt(i);
            // 检查字符是否在支持的范围内
            if (isSupportedChar(c)) {
                filteredText.append(c);
            } else {
                // 不支持的字符用空格替换
                filteredText.append(' ');
            }
        }
        safeText = filteredText.toString().replaceAll("\\s+", " ").trim();

        // PDF页面宽度（从参数传入，使用实际页面宽度）
        float rightMargin = 20.0f;  // 增加右边距，给文本更多空间

        // 设置字体大小
        float fontSize = TRANSLATION_ZH_FONT_SIZE_PT;
        float lineHeight = TRANSLATION_ZH_LINE_HEIGHT_PT;

        // 中文字符宽度约为fontSize，考虑间距后每个字符占用的宽度约为1.1*fontSize（更精确的估算）
        float charWidth = fontSize * 1.1f;

        // 计算从x位置到右边缘的可用宽度
        float availableWidth = pageWidth - x - rightMargin;

        // 计算每行可以容纳的字符数（从起始位置x到右边缘），至少为1避免 wrapText 死循环导致 OOM
        int charsPerLine = Math.max(1, (int) (availableWidth / charWidth));

        // 分割文本为多行
        List<String> lines = wrapText(safeText, charsPerLine);

        // 直接绘制文本，不需要重叠检测
        float currentY = pdfBoxY;
        float currentFontSize = fontSize;
        float currentLineHeight = lineHeight;

        for (String line : lines) {
            contentStream.setNonStrokingColor(java.awt.Color.BLACK);
            contentStream.beginText();
            contentStream.setFont(chineseFont, currentFontSize);
            contentStream.newLineAtOffset(x, currentY);
            contentStream.showText(line);
            contentStream.endText();

            // 移动到下一行的默认位置
            currentY -= currentLineHeight;
        }
    }


    /**
     * 检查字符是否被字体支持
     * 支持：中文字符、英文字母、数字、常用标点符号、空格
     */
    private static boolean isSupportedChar(char c) {
        // 空格
        if (c == ' ') return true;
        // 英文字母和数字
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')) return true;
        // 中文字符范围（CJK统一汉字）
        if (c >= 0x4E00 && c <= 0x9FFF) return true;
        // 常用标点符号
        if (c == '.' || c == ',' || c == ';' || c == ':' || c == '!' || c == '?' ||
                c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' ||
                c == '-' || c == '_' || c == '+' || c == '=' || c == '*' || c == '/' ||
                c == '"' || c == '\'' || c == '`' || c == '~' || c == '@' || c == '#' ||
                c == '$' || c == '%' || c == '^' || c == '&' || c == '|' || c == '\\' ||
                c == '<' || c == '>') return true;
        // 中文标点符号
        if (c == '。' || c == '，' || c == '；' || c == '：' || c == '！' || c == '？' ||
                c == '（' || c == '）' || c == '【' || c == '】' || c == '《' || c == '》' ||
                c == '「' || c == '」' || c == '『' || c == '』' || c == '、' || c == '…' ||
                c == '—' || c == '·' || c == '…') return true;
        return false;
    }

    /**
     * 将文本换行（智能换行，避免在词中间分割）
     */
    private static List<String> wrapText(String text, int maxCharsPerLine) {
        List<String> lines = new ArrayList<>();
        // 防止每行字符数<=0导致死循环（availableWidth过小或为负时会触发 OOM）
        if (maxCharsPerLine <= 0) {
            maxCharsPerLine = 1;
        }
        int pos = 0;
        while (pos < text.length()) {
            // 如果剩余文本长度小于等于maxCharsPerLine，直接添加
            if (pos + maxCharsPerLine >= text.length()) {
                lines.add(text.substring(pos));
                break;
            }

            // 尝试找到一个合适的断点
            int endPos = pos + maxCharsPerLine;

            // 优先在标点符号处断行（中文和英文标点）
            int bestBreakPos = findBestBreakPoint(text, pos, endPos);

            if (bestBreakPos > pos) {
                // 找到了合适的断点
                String line = text.substring(pos, bestBreakPos).trim();
                if (!line.isEmpty()) {
                    lines.add(line);
                }
                pos = bestBreakPos;
                // 跳过空格和标点后的空格
                while (pos < text.length() && (text.charAt(pos) == ' ' || text.charAt(pos) == '\n')) {
                    pos++;
                }
            } else {
                // 没有找到合适的断点，强制在maxCharsPerLine处分割（至少前进1个字符，防止死循环）
                int advance = Math.max(1, Math.min(maxCharsPerLine, text.length() - pos));
                String line = text.substring(pos, pos + advance);
                lines.add(line);
                pos = pos + advance;
            }
        }

        return lines;
    }

    /**
     * 查找最佳断点位置
     * 优先级：1. 句号、问号、感叹号  2. 分号、冒号  3. 逗号  4. 空格
     */
    private static int findBestBreakPoint(String text, int startPos, int endPos) {
        int bestPos = -1;
        int bestPriority = -1;

        // 从后往前查找，优先匹配优先级高的标点
        for (int i = endPos - 1; i >= startPos; i--) {
            char c = text.charAt(i);
            int priority = -1;

            // 优先级1：句号、问号、感叹号（最高优先级）
            if (c == '。' || c == '.' || c == '？' || c == '?' || c == '！' || c == '!') {
                priority = 4;
            }
            // 优先级2：分号、冒号
            else if (c == '；' || c == ';' || c == '：' || c == ':') {
                priority = 3;
            }
            // 优先级3：逗号
            else if (c == '，' || c == ',') {
                priority = 2;
            }
            // 优先级4：空格
            else if (c == ' ') {
                priority = 1;
            }

            // 如果找到更高优先级的断点，更新
            if (priority > bestPriority) {
                bestPriority = priority;
                bestPos = i + 1; // 断点在标点符号之后

                // 如果找到最高优先级（句号等），可以立即返回
                if (priority == 4) {
                    return bestPos;
                }
            }
        }

        return bestPos;
    }

    // ============================================================
    // OCR功能实现
    // ============================================================

    /**
     * 初始化Tesseract OCR引擎
     */
    private static Tesseract initializeTesseract() throws Exception {
        if (tesseract == null) {
            tesseract = new Tesseract();

            // 尝试找到Tesseract数据路径
            String tessdataPath = findTessdataPath();
            if (tessdataPath != null) {
                tesseract.setDatapath(tessdataPath);
                System.out.println("📁 使用Tesseract数据路径: " + tessdataPath);
            } else {
                // 如果找不到路径，提供详细的安装说明
                System.err.println("❌ 未找到Tesseract数据文件路径！");
                System.err.println("");
                System.err.println("📋 请按照以下步骤安装Tesseract OCR：");
                System.err.println("   1. 下载安装程序: https://github.com/UB-Mannheim/tesseract/wiki");
                System.err.println("   2. 安装到默认路径: C:\\Program Files\\Tesseract-OCR");
                System.err.println("   3. 确保tessdata文件夹存在: C:\\Program Files\\Tesseract-OCR\\tessdata");
                System.err.println("   4. 或者设置环境变量 TESSDATA_PREFIX 指向tessdata文件夹的父目录");
                System.err.println("");
                System.err.println("💡 如果已安装但路径不同，请修改代码中的 findTessdataPath() 方法");
                throw new Exception("Tesseract数据文件未找到。请先安装Tesseract OCR。");
            }

            // 设置语言（英文）
            tesseract.setLanguage("eng");

            // 设置OCR模式
            // 3 = 完全自动页面分割，但不进行OCR（PSM_AUTO_OSD）
            // 6 = 假设统一的文本块（PSM_UNIFORM_BLOCK）
            // 11 = 稀疏文本（PSM_SPARSE_TEXT）- 适合表格和复杂布局
            // 13 = 原始行，使用Tesseract LSTM引擎（PSM_RAW_LINE）
            // 使用模式11（稀疏文本）可以更好地识别表格和复杂布局中的文本
            tesseract.setPageSegMode(11);

            // 设置OCR引擎模式（3 = 默认，基于LSTM神经网络）
            tesseract.setOcrEngineMode(3);

            System.out.println("✅ Tesseract OCR引擎初始化成功");
        }
        return tesseract;
    }

    /**
     * 查找Tesseract数据文件路径
     */
    private static String findTessdataPath() {
        // 常见的Tesseract安装路径
        String[] possiblePaths = {
                "C:/Program Files/Tesseract-OCR/tessdata",
                "C:/Program Files (x86)/Tesseract-OCR/tessdata",
                "C:/Tesseract-OCR/tessdata",
                "D:/Program Files/Tesseract-OCR/tessdata",
                "D:/Program Files (x86)/Tesseract-OCR/tessdata",
                "D:/Tesseract-OCR/tessdata",
                "./tessdata",  // 当前目录
                "../tessdata"   // 上级目录
        };

        // 检查环境变量
        String envPath = System.getenv("TESSDATA_PREFIX");
        if (envPath != null && !envPath.isEmpty()) {
            String tessdataPath = envPath.endsWith("/") || envPath.endsWith("\\")
                    ? envPath + "tessdata"
                    : envPath + File.separator + "tessdata";
            if (new File(tessdataPath).exists()) {
                return tessdataPath;
            }
        }

        // 遍历可能的路径
        for (String path : possiblePaths) {
            File tessdataDir = new File(path);
            if (tessdataDir.exists() && tessdataDir.isDirectory()) {
                // 检查是否包含eng.traineddata文件
                File engFile = new File(tessdataDir, "eng.traineddata");
                if (engFile.exists()) {
                    return path;
                }
            }
        }

        return null;
    }

    /**
     * 将 PDF 页渲染为用于 OCR 的位图（与 {@link #extractTextWithOCR} 一致）
     */
    private static BufferedImage renderPageImageForOcr(PDDocument document, int pageIndex) throws IOException {
        PDFRenderer renderer = new PDFRenderer(document);
        BufferedImage image = renderer.renderImageWithDPI(pageIndex, OCR_DPI, ImageType.RGB);
        return preprocessImage(image);
    }

    /**
     * 页面资源中是否存在足够大的嵌入位图（用于判断是否做混合页补充 OCR）
     */
    private static boolean pageHasRasterImages(PDPage page) throws IOException {
        PDResources resources = page.getResources();
        if (resources == null) return false;
        for (COSName name : resources.getXObjectNames()) {
            PDXObject xObject = resources.getXObject(name);
            if (xObject instanceof PDImageXObject) {
                PDImageXObject img = (PDImageXObject) xObject;
                long pixels = (long) img.getWidth() * (long) img.getHeight();
                if (pixels >= MIN_RASTER_IMAGE_PIXELS) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * 若页面存在足够大的位图，且解析到的绘制框均在「装饰区」（页脚/顶条），且文本层已有足够字数，则跳过混合全页 OCR。
     */
    private static boolean shouldSkipHybridOcrForDecorativeEmbeddedRastersOnly(
            PDPage page, List<CoordinateTextStripper.TextItem> textLayerItems) throws IOException {
        if (textLayerItems == null || textLayerItems.isEmpty()) {
            return false;
        }
        int chars = 0;
        for (CoordinateTextStripper.TextItem ti : textLayerItems) {
            if (ti != null && ti.text != null) {
                chars += ti.text.length();
            }
        }
        if (chars < HYBRID_SKIP_DECORATIVE_RASTER_MIN_TEXT_CHARS) {
            return false;
        }
        List<Rectangle2D.Float> bounds = collectLargeEmbeddedImageBoundsInPageSpace(page);
        if (bounds.isEmpty()) {
            return false;
        }
        PDRectangle crop = page.getCropBox();
        float w = crop.getWidth();
        float h = crop.getHeight();
        return rasterBoundsOnlyInHybridDecorativeZones(bounds, w, h);
    }

    /**
     * 解析页面内容流，收集「像素面积 ≥ {@link #MIN_RASTER_IMAGE_PIXELS}」的每次 drawImage 在用户空间的包围盒。
     */
    private static List<Rectangle2D.Float> collectLargeEmbeddedImageBoundsInPageSpace(PDPage page) {
        try {
            HybridEmbeddedImageBoundsCollector collector = new HybridEmbeddedImageBoundsCollector(page);
            collector.processPage(page);
            return new ArrayList<>(collector.largeImageBounds);
        } catch (Exception e) {
            System.out.println("  [混合OCR] 解析嵌入图绘制位置失败，不启用「装饰区跳过」策略: " + e.getMessage());
            return Collections.emptyList();
        }
    }

    private static boolean rasterBoundsOnlyInHybridDecorativeZones(
            List<Rectangle2D.Float> bounds, float pageW, float pageH) {
        if (bounds == null || bounds.isEmpty() || pageW <= 0 || pageH <= 0) {
            return false;
        }
        for (Rectangle2D.Float r : bounds) {
            if (r == null || r.getWidth() <= 0 || r.getHeight() <= 0) {
                continue;
            }
            if (!hybridRasterInDecorativeCornerZone(r, pageW, pageH)) {
                return false;
            }
        }
        return true;
    }

    /**
     * PDF 用户空间：原点在左下，y 向上。校徽多在<strong>右下角</strong>（高 x、低 y）；顶栏装饰线为窄高条贴顶。
     * 条件故意偏严，避免把中下部的课程示意图当成「装饰图」而跳过混合 OCR。
     */
    private static boolean hybridRasterInDecorativeCornerZone(Rectangle2D.Float r, float pageW, float pageH) {
        double cx = r.getCenterX();
        double cy = r.getCenterY();
        boolean rightFooter = cx >= pageW * 0.56f && cy <= pageH * 0.36f;
        boolean topBar = r.getHeight() <= pageH * 0.085f && r.getMinY() >= pageH * 0.88f;
        return rightFooter || topBar;
    }

    /**
     * 根据文本层 TextItem 估算在渲染图上的覆盖矩形（像素坐标，原点在左上），用于剔除重复 OCR。
     * <p>
     * 注意：本项目中 {@link CoordinateTextStripper} 在多数课件上为「自上而下」Y（与 detectCoordinateSystem
     * 中「Y 值小在上」一致）：y 从页面顶向下递增，与位图从上到下的行坐标一致。
     * 因此行顶像素应为 y_px ≈ ti.y * imageHeight / pageHeight，切勿使用 imageHeight - ti.y * …（那是标准 PDF 底向上坐标）。
     */
    private static List<Rectangle> buildTextLayerCoverageInImageSpace(
            List<CoordinateTextStripper.TextItem> textLayerItems,
            float pageWidth, float pageHeight, int imageWidth, int imageHeight) {
        List<Rectangle> rects = new ArrayList<>();
        if (textLayerItems == null || textLayerItems.isEmpty()) return rects;
        float sx = imageWidth / pageWidth;
        float sy = imageHeight / pageHeight;
        int pad = (int) Math.max(4, Math.round(6 * Math.min(sx, sy)));
        for (CoordinateTextStripper.TextItem ti : textLayerItems) {
            if (ti == null || ti.text == null || ti.text.trim().isEmpty()) continue;
            int left = (int) Math.floor(ti.x * sx) - pad;
            int w = (int) Math.max(24, Math.round(Math.max(ti.text.length(), 1) * 6 * sx)) + 2 * pad;
            // 行高约 15pt 映射到像素，略放大以免漏剔
            int h = (int) Math.max(18, Math.round(15 * sy)) + 2 * pad;
            // 自上而下 Y → 位图从上到下的行顶
            int topOfLine = (int) Math.round(ti.y * imageHeight / pageHeight);
            left = Math.max(0, left);
            topOfLine = Math.max(0, topOfLine);
            w = Math.min(imageWidth - left, w);
            h = Math.min(imageHeight - topOfLine, h);
            if (w > 0 && h > 0) {
                rects.add(new Rectangle(left, topOfLine, w, h));
            }
        }
        return rects;
    }

    /**
     * 若 OCR 词框与文本层覆盖矩形重叠面积超过阈值，则认为该词来自文本层，应丢弃
     */
    private static boolean ocrWordIsOutsideTextLayer(Rectangle wordBox, List<Rectangle> textLayerRects) {
        if (wordBox == null || wordBox.width <= 0 || wordBox.height <= 0) return false;
        if (textLayerRects == null || textLayerRects.isEmpty()) return true;
        int oArea = wordBox.width * wordBox.height;
        if (oArea <= 0) return false;
        int covered = 0;
        for (Rectangle c : textLayerRects) {
            if (!wordBox.intersects(c)) continue;
            Rectangle inter = wordBox.intersection(c);
            covered += inter.width * inter.height;
        }
        return ((double) covered / (double) oArea) < OCR_TEXT_LAYER_OVERLAP_THRESHOLD;
    }

    /**
     * 嵌入图行级 OCR 常见噪点修正：项目符号残片、e/1s 误识、乘号等（不改变坐标）
     */
    private static String cleanupHybridEmbeddedOcrLine(String text) {
        if (text == null) return "";
        String t = text.trim();
        // 行首单独的 e/E 多为 • 或 (i) 的残片
        t = t.replaceFirst("(?i)^[eE]\\s+", "");
        // 徽标旁常见：oe + 校名
        t = t.replaceFirst("(?i)^oe\\s+", "");
        t = t.replaceFirst("^[''‘'ʼ´`ˊ]+\\s*", "");
        // 「I」易被识别为斜杠：/nputs → Inputs
        t = t.replaceFirst("(?i)^/nputs\\b", "Inputs");
        // ❑ 常被误识为 UO) / LU) / L) / O) 等（方形项目符号边角被当成字母）
        t = t.replaceFirst("(?i)^u[oO]\\)\\s*", "");
        t = t.replaceFirst("(?i)^l[uU]\\)\\s*", "");
        t = t.replaceFirst("(?i)^l\\)\\s*", "");
        // ❑ 常被误识为 O) / 数字+括号；校徽旁常见 PE) / PЕ) 等
        t = t.replaceFirst("(?i)^[o0q]\\)\\s*", "");
        t = t.replaceFirst("(?i)^pe\\)\\s*", "");
        // 「is」常被识别成 1s
        t = t.replaceAll("(?i)\\b1s\\b", "is");
        t = t.replace('«', '×');
        return t.trim();
    }

    /**
     * 混合页：全页 OCR 后去掉与 PDF 文本层位置重叠的词，得到「仅出现在位图里」的文字
     */
    private static List<CoordinateTextStripper.TextItem> extractImageEmbeddedTextViaOCR(
            PDDocument document, PDPage page, int pageIndex,
            List<CoordinateTextStripper.TextItem> textLayerItems) throws Exception {

        Tesseract tesseract;
        try {
            tesseract = initializeTesseract();
        } catch (Exception e) {
            throw new Exception("OCR引擎初始化失败: " + e.getMessage(), e);
        }

        BufferedImage image = renderPageImageForOcr(document, pageIndex);
        float pageWidth = page.getMediaBox().getWidth();
        float pageHeight = page.getMediaBox().getHeight();
        int imgW = image.getWidth();
        int imgH = image.getHeight();

        System.out.println("  [混合OCR] 全页渲染，按「词框」识别（RIL_WORD），水平大间隙拆成多段，并剔除与文本层重叠的词...");
        java.util.List<net.sourceforge.tess4j.Word> words;
        tesseract.setPageSegMode(TESS_HYBRID_EMBEDDED_PAGE_SEG_MODE);
        try {
            words = tesseract.getWords(image, TESS_PAGE_ITERATOR_WORD);
        } finally {
            tesseract.setPageSegMode(TESS_DEFAULT_PAGE_SEG_MODE);
        }
        if (words == null || words.isEmpty()) {
            return new ArrayList<>();
        }

        List<Rectangle> coverage = buildTextLayerCoverageInImageSpace(
                textLayerItems, pageWidth, pageHeight, imgW, imgH);

        List<net.sourceforge.tess4j.Word> kept = new ArrayList<>();
        int droppedByOverlap = 0;
        for (net.sourceforge.tess4j.Word w : words) {
            if (w == null || w.getText() == null || w.getText().trim().isEmpty()) continue;
            Rectangle bbox = w.getBoundingBox();
            if (bbox == null) continue;
            if (ocrWordIsOutsideTextLayer(bbox, coverage)) {
                kept.add(w);
            } else {
                droppedByOverlap++;
            }
        }

        System.out.println("  [混合OCR] 全页 " + words.size() + " 词 → 剔除文本层重叠后 " + kept.size() + " 词"
                + (droppedByOverlap > 0 ? "（误重叠剔除 " + droppedByOverlap + " 词，若偏多请检查覆盖框）" : ""));

        List<CoordinateTextStripper.TextItem> parsed = hybridSplitOcrWordsToTextItems(
                kept, pageWidth, pageHeight, imgW, imgH);
        // 自上而下排序，保证分组与阅读顺序稳定
        parsed.sort((a, b) -> Float.compare(a.y, b.y));
        for (CoordinateTextStripper.TextItem it : parsed) {
            if (it != null && it.text != null) {
                it.text = cleanupHybridEmbeddedOcrLine(it.text);
            }
        }
        parsed.removeIf(it -> it == null || it.text == null || it.text.trim().isEmpty());
        List<CoordinateTextStripper.TextItem> deduped = filterHybridOcrDuplicatesOfTextLayer(parsed, textLayerItems);
        if (deduped.size() < parsed.size()) {
            System.out.println("  [混合OCR] 与文本层语义重复再剔除 " + (parsed.size() - deduped.size()) + " 项，剩余 " + deduped.size() + " 项");
        }
        return deduped;
    }

    /**
     * 去掉与 PDF 文本层在垂直位置接近且内容相同或互为子串的 OCR 片段（避免重复翻译标题、页码等）
     */
    private static List<CoordinateTextStripper.TextItem> filterHybridOcrDuplicatesOfTextLayer(
            List<CoordinateTextStripper.TextItem> ocrItems,
            List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (ocrItems == null || ocrItems.isEmpty()) return ocrItems;
        if (textLayerItems == null || textLayerItems.isEmpty()) return ocrItems;
        List<CoordinateTextStripper.TextItem> out = new ArrayList<>();
        for (CoordinateTextStripper.TextItem o : ocrItems) {
            if (hybridOcrItemDuplicatesTextLayer(o, textLayerItems)) {
                System.out.println("  [混合OCR] 丢弃与文本层重复的片段: \"" +
                        (o.text.length() > 60 ? o.text.substring(0, 60) + "..." : o.text) + "\"");
                continue;
            }
            out.add(o);
        }
        return out;
    }

    /**
     * 混合 OCR 片段中的词是否按顺序、均以整词形式出现在同一 haystack 中（允许中间隔其他词）。
     * 用于识别「and issues」对应文本层「… and usability issues …」一类非连续但同源的重影。
     */
    private static boolean hybridOcrPhraseWordsAllInOrderInHaystack(String haystack, String phraseNorm) {
        if (haystack == null || phraseNorm == null || phraseNorm.isEmpty()) {
            return false;
        }
        String[] words = phraseNorm.trim().split("\\s+");
        if (words.length == 0) {
            return false;
        }
        int pos = 0;
        for (String w : words) {
            if (w.isEmpty()) {
                continue;
            }
            Pattern p = Pattern.compile("(?U)(?<![\\p{L}\\p{N}])" + Pattern.quote(w) + "(?![\\p{L}\\p{N}])");
            Matcher m = p.matcher(haystack);
            if (!m.find(pos)) {
                return false;
            }
            pos = m.end();
        }
        return true;
    }

    /**
     * 全页渲染抗锯齿时，正文词在「与文本层框重叠剔除」失败后仍会作为零散 OCR 出现；
     * 在 OCR 块竖直邻域内拼接的文本层串上做整词/顺序匹配即可判为重复，无需再译。
     */
    private static boolean hybridOcrSubsumedByNearbyTextLayer(
            CoordinateTextStripper.TextItem o, String otNorm,
            List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || otNorm == null || otNorm.isEmpty() || textLayerItems == null) {
            return false;
        }
        if (otNorm.length() > 52) {
            return false;
        }
        String fullPage = buildFullTextLayerNormalizedSorted(textLayerItems);
        if (fullPage.length() < 50) {
            return false;
        }
        final float slackY = 145f;
        String near = buildTextLayerConcatNormalizedNearY(textLayerItems, o.y, slackY);
        String haystack = near.length() >= 32 ? near : fullPage;
        if (otNorm.contains(" ")) {
            return hybridOcrPhraseWordsAllInOrderInHaystack(haystack, otNorm);
        }
        if (!hybridWholeWordInBoundedText(otNorm, haystack)) {
            return false;
        }
        if (otNorm.length() >= 3) {
            return true;
        }
        return otNorm.length() == 2 && HYBRID_DEDUP_STOPWORDS.contains(otNorm);
    }

    private static boolean hybridOcrItemDuplicatesTextLayer(
            CoordinateTextStripper.TextItem o, List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || o.text == null) return false;
        // 标题旁单独 OCR 出的「(FSM)」等与文本层标题重复
        if (hybridOcrIsRedundantParentheticalAcronym(o, textLayerItems)) {
            return true;
        }
        String ot = normalizeTextForHybridDedup(o.text);
        if (hybridOcrSubsumedByNearbyTextLayer(o, ot, textLayerItems)) {
            return true;
        }
        if (ot.length() < 4) return false;
        // 校徽等位图旁：整页渲染反锯齿导致正文词被再次 OCR 成零散「影子词」（Moore、Machines、words、causal）
        if (hybridOcrIsRenderedTextShadowOfTextLayer(o, ot, textLayerItems)) {
            return true;
        }
        // 内容词重叠（含 fsmss/fsms 等）：解决「FSMss is drawn notation」与文本层整句仅部分 OCR 重合、关键词规则凑不齐 2 条短语的问题
        if (hybridOcrTokenOverlapDuplicatesTextLayer(o, ot, textLayerItems)) {
            return true;
        }
        if (ot.length() < 5) return false;
        // 多词组同时命中且 Y 接近：覆盖「FSMss… graphical notation」与文本层「FSMs is drawn…」等 OCR 变形
        if (hybridOcrOverlapsTextLayerByKeyPhrases(o, ot, textLayerItems)) {
            return true;
        }
        // OCR 的 ASCII「FSM("States;...」与文本层数学体 𝐹𝑆𝑀("States;...」视为同一条公式行，避免重复译
        if (ot.startsWith("fsm(")) {
            for (CoordinateTextStripper.TextItem t : textLayerItems) {
                if (t == null || t.text == null) continue;
                String tt = normalizeTextForHybridDedup(t.text);
                if (tt.contains("states") && tt.contains("inputs") && tt.contains("outputs")
                        && tt.contains("initialstate")) {
                    return true;
                }
            }
        }
        /*
         * 语义去重：❑ 常被误识为 O)、LU) 等，Y 与文本层也可能差几十像素（渲染 vs stripper）
         * 去掉项目符号与 OCR 前缀后若核心句相同，则视为与文本层重复，避免第二遍再译一遍。
         */
        final float semanticYSlack = 130f;
        String oCore = stripHybridBulletNoiseForDedup(ot);
        if (oCore.length() >= 10) {
            for (CoordinateTextStripper.TextItem t : textLayerItems) {
                if (t == null || t.text == null) continue;
                String tt = normalizeTextForHybridDedup(t.text);
                String tCore = stripHybridBulletNoiseForDedup(tt);
                if (tCore.length() < 10) continue;
                if (Math.abs(o.y - t.y) > semanticYSlack) continue;
                if (oCore.equals(tCore)) return true;
                if (oCore.contains(tCore) || tCore.contains(oCore)) {
                    int minL = Math.min(oCore.length(), tCore.length());
                    int maxL = Math.max(oCore.length(), tCore.length());
                    if (maxL > 0 && (double) minL / (double) maxL >= 0.82) return true;
                }
            }
        }
        for (CoordinateTextStripper.TextItem t : textLayerItems) {
            if (t == null || t.text == null) continue;
            String tt = normalizeTextForHybridDedup(t.text);
            if (tt.length() < 5) continue;
            if (Math.abs(o.y - t.y) > 60f) continue;
            if (ot.equals(tt)) return true;
            if (ot.length() >= 14 && tt.contains(ot)) return true;
            if (tt.length() >= 14 && ot.contains(tt)) return true;
        }
        return false;
    }

    /**
     * 用若干英文短语同时出现 + 竖直位置接近，判定混合 OCR 行与文本层某条为同一内容（应对严重 OCR 变形）
     */
    private static boolean hybridOcrOverlapsTextLayerByKeyPhrases(
            CoordinateTextStripper.TextItem o, String otNorm, List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || otNorm == null || textLayerItems == null) return false;
        final String[] phrases = {
                "graphical notation", "drawn using", "finite state", "state machine",
                "jiaotong", "liverpool", "university"
        };
        int oHits = 0;
        for (String p : phrases) {
            if (otNorm.contains(p)) oHits++;
        }
        // OCR 常丢掉 graphical/using，仅余 drawn + notation，与文本层仍属同一句
        if (oHits < 2 && otNorm.contains("drawn") && otNorm.contains("notation")) {
            oHits = 2;
        }
        if (oHits < 2) return false;
        final float slackY = 200f;
        String combinedNear = buildTextLayerConcatNormalizedNearY(textLayerItems, o.y, slackY);
        int tHits = 0;
        for (String p : phrases) {
            if (combinedNear.contains(p)) tHits++;
        }
        if (tHits >= 2) {
            return true;
        }
        for (CoordinateTextStripper.TextItem t : textLayerItems) {
            if (t == null || t.text == null) continue;
            if (Math.abs(o.y - t.y) >= slackY) continue;
            String tt = normalizeTextForHybridDedup(t.text);
            int hitsOne = 0;
            for (String p : phrases) {
                if (tt.contains(p)) hitsOne++;
            }
            if (hitsOne >= 2) {
                return true;
            }
        }
        return false;
    }

    /**
     * 混合 OCR 去重：去掉行首项目符号、O)/LU)/) 等误识，得到可与文本层对比的「核心」小写串
     */
    private static String stripHybridBulletNoiseForDedup(String normalizedLower) {
        if (normalizedLower == null) return "";
        String t = normalizedLower.trim();
        t = t.replaceFirst("(?i)^lu\\)\\s*", "");
        t = t.replaceFirst("(?i)^l[\\)\\]\\.]\\s*", "");
        t = t.replaceFirst("(?i)^[o0q]\\)\\s*", "");
        t = t.replaceFirst("^\\)+\\s*", "");
        t = t.replaceFirst("^[^a-z0-9]+", "");
        return t.trim();
    }

    private static String normalizeTextForHybridDedup(String s) {
        if (s == null) return "";
        return s.replaceAll("\\s+", " ").trim().toLowerCase()
                .replace("”", "\"").replace("“", "\"");
    }

    /** 混合 OCR 去重：去掉功能词后用于与文本层比对的「实词」 */
    private static final Set<String> HYBRID_DEDUP_STOPWORDS = new HashSet<>(Arrays.asList(
            "the", "a", "an", "to", "of", "and", "or", "in", "on", "at", "for", "is", "are", "was", "were",
            "be", "been", "may", "can", "could", "will", "would", "should", "must", "it", "its", "this", "that",
            "each", "there", "then", "than", "into", "from", "with", "by", "as", "also", "not", "no",
            "so", "if", "we", "you", "all", "any", "both", "per", "up", "out"));

    private static List<String> hybridDedupContentTokens(String normalizedLower) {
        if (normalizedLower == null || normalizedLower.isEmpty()) return Collections.emptyList();
        String[] parts = normalizedLower.split("[^a-z0-9]+");
        List<String> list = new ArrayList<>();
        for (String p : parts) {
            if (p.isEmpty()) continue;
            if (p.length() < 3 && !p.equals("fsm")) continue;
            if (HYBRID_DEDUP_STOPWORDS.contains(p)) continue;
            list.add(p);
        }
        return list;
    }

    /**
     * 将竖直位置接近 o.y 的文本层片段按 X 拼成一行再规范化，避免 ❑ 与正文分属不同 TextItem 时无法比对整句。
     */
    /**
     * 全页文本层串接后规范化，用于判断 OCR 词是否已在某处正文出现。
     */
    private static String buildFullTextLayerNormalizedSorted(List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (textLayerItems == null || textLayerItems.isEmpty()) {
            return "";
        }
        List<CoordinateTextStripper.TextItem> copy = new ArrayList<>();
        for (CoordinateTextStripper.TextItem ti : textLayerItems) {
            if (ti != null && ti.text != null && !ti.text.trim().isEmpty()) {
                copy.add(ti);
            }
        }
        copy.sort(Comparator.comparingDouble((CoordinateTextStripper.TextItem ti) -> (double) ti.y)
                .thenComparingDouble(ti -> (double) ti.x));
        StringBuilder sb = new StringBuilder();
        for (CoordinateTextStripper.TextItem ti : copy) {
            if (sb.length() > 0) {
                sb.append(' ');
            }
            sb.append(ti.text.trim());
        }
        return normalizeTextForHybridDedup(sb.toString());
    }

    private static boolean hybridWholeWordInBoundedText(String token, String textLower) {
        if (token == null || token.length() < 2 || textLower == null || textLower.isEmpty()) {
            return false;
        }
        return Pattern.compile("(?u)(?<![\\p{L}\\p{N}])" + Pattern.quote(token) + "(?![\\p{L}\\p{N}])")
                .matcher(textLower).find();
    }

    /**
     * 短片段、实词均作为完整词出现在文本层中，且在竖直带内能对应到含这些词的原文 → 视为渲染图影子，不补充翻译。
     */
    private static boolean hybridOcrIsRenderedTextShadowOfTextLayer(
            CoordinateTextStripper.TextItem o, String otNorm,
            List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || otNorm == null || textLayerItems == null) {
            return false;
        }
        String ot = otNorm.replaceAll("[,;\\.]+$", "").trim();
        if (ot.length() > HYBRID_SHADOW_OCR_MAX_FRAGMENT_LEN) {
            return false;
        }
        List<String> tokens = hybridDedupContentTokens(ot);
        if (tokens.isEmpty() || tokens.size() > 5) {
            return false;
        }
        int meaningful = 0;
        for (String t : tokens) {
            if (t.length() >= 3) {
                meaningful++;
            }
        }
        if (meaningful == 0) {
            return false;
        }
        String fullPage = buildFullTextLayerNormalizedSorted(textLayerItems);
        for (String tok : tokens) {
            if (tok.length() < 3) {
                continue;
            }
            if (!hybridWholeWordInBoundedText(tok, fullPage)) {
                return false;
            }
        }
        final float slackY = 178f;
        String near = buildTextLayerConcatNormalizedNearY(textLayerItems, o.y, slackY);
        for (String tok : tokens) {
            if (tok.length() < 3) {
                continue;
            }
            if (hybridWholeWordInBoundedText(tok, near)) {
                continue;
            }
            boolean ok = false;
            for (CoordinateTextStripper.TextItem t : textLayerItems) {
                if (t == null || t.text == null) {
                    continue;
                }
                String line = normalizeTextForHybridDedup(t.text);
                if (!hybridWholeWordInBoundedText(tok, line)) {
                    continue;
                }
                if (Math.abs(o.y - t.y) <= slackY) {
                    ok = true;
                    break;
                }
            }
            if (!ok) {
                return false;
            }
        }
        if (hybridOcrShortFragmentIsClearlyBelowTextLayerSources(o, tokens, textLayerItems)) {
            return false;
        }
        return true;
    }

    /**
     * 短片段的实词若能全部作为整词出现在文本层<strong>同一行</strong>，但 OCR 的 Y 已明显低于该行，
     * 则多为「上方公式/标题」与「下方嵌入图说明」的上下关系，不是抗锯齿重影。
     */
    private static boolean hybridOcrShortFragmentIsClearlyBelowTextLayerSources(
            CoordinateTextStripper.TextItem o, List<String> tokens,
            List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || tokens == null || textLayerItems == null) {
            return false;
        }
        List<String> need = new ArrayList<>();
        for (String tok : tokens) {
            if (tok != null && tok.length() >= 3) {
                need.add(tok);
            }
        }
        if (need.isEmpty()) {
            return false;
        }
        float minY = Float.POSITIVE_INFINITY;
        for (CoordinateTextStripper.TextItem t : textLayerItems) {
            if (t == null || t.text == null) {
                continue;
            }
            String line = normalizeTextForHybridDedup(t.text);
            boolean all = true;
            for (String tok : need) {
                if (!hybridWholeWordInBoundedText(tok, line)) {
                    all = false;
                    break;
                }
            }
            if (all) {
                minY = Math.min(minY, t.y);
            }
        }
        if (minY == Float.POSITIVE_INFINITY) {
            return false;
        }
        return o.y > minY + HYBRID_SHADOW_MIN_VERTICAL_SEP_BELOW_TEXT_LAYER_PT;
    }

    private static String buildTextLayerConcatNormalizedNearY(
            List<CoordinateTextStripper.TextItem> textLayerItems, float yRef, float slackY) {
        if (textLayerItems == null || textLayerItems.isEmpty()) return "";
        List<CoordinateTextStripper.TextItem> near = new ArrayList<>();
        for (CoordinateTextStripper.TextItem ti : textLayerItems) {
            if (ti == null || ti.text == null || ti.text.trim().isEmpty()) continue;
            if (Math.abs(ti.y - yRef) > slackY) continue;
            near.add(ti);
        }
        if (near.isEmpty()) return "";
        near.sort(Comparator.comparingDouble(ti -> ti.x));
        StringBuilder sb = new StringBuilder();
        for (CoordinateTextStripper.TextItem ti : near) {
            if (sb.length() > 0) sb.append(' ');
            sb.append(ti.text.trim());
        }
        return normalizeTextForHybridDedup(sb.toString());
    }

    private static boolean hybridOcrContentTokensMatchNormalizedLine(List<String> oTokens, String ttNorm) {
        if (oTokens == null || oTokens.size() < 2 || ttNorm == null || ttNorm.length() < 8) return false;
        int matched = 0;
        boolean hasLongTokenHit = false;
        for (String tok : oTokens) {
            if (!hybridDedupTokenMatchesLine(tok, ttNorm)) continue;
            matched++;
            if (tok.length() >= 4) {
                hasLongTokenHit = true;
            }
        }
        int need = oTokens.size() <= 2 ? oTokens.size() : Math.max(2, (int) Math.ceil(oTokens.size() * 0.51));
        return matched >= need && hasLongTokenHit;
    }

    /**
     * 混合 OCR 片段与文本层某行在竖直方向接近，且多个实词命中（含 fsm↔fsmss 等轻微变形），视为重复翻译源。
     */
    private static boolean hybridOcrTokenOverlapDuplicatesTextLayer(
            CoordinateTextStripper.TextItem o, String otNorm, List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || textLayerItems == null || otNorm == null) return false;
        List<String> oTokens = hybridDedupContentTokens(otNorm);
        if (oTokens.size() < 2) return false;
        String fullPageNorm = buildFullTextLayerNormalizedSorted(textLayerItems);
        if (hybridOcrHasSubstantiveTokenOutsideTextLayer(oTokens, fullPageNorm)) {
            return false;
        }
        final float slackY = 140f;
        String combined = buildTextLayerConcatNormalizedNearY(textLayerItems, o.y, slackY);
        if (hybridOcrContentTokensMatchNormalizedLine(oTokens, combined)) {
            return true;
        }
        for (CoordinateTextStripper.TextItem t : textLayerItems) {
            if (t == null || t.text == null) continue;
            if (Math.abs(o.y - t.y) > slackY) continue;
            String tt = normalizeTextForHybridDedup(t.text);
            if (hybridOcrContentTokensMatchNormalizedLine(oTokens, tt)) {
                return true;
            }
        }
        return false;
    }

    /**
     * 若 OCR 行含有长度≥4 的实词在整页文本层中完全找不到，则该行很可能是嵌入图里的说明句，
     * 不应因与公式行共享 states/inputs/outputs/update 等字段名而被 token 重叠去重误杀。
     */
    private static boolean hybridOcrHasSubstantiveTokenOutsideTextLayer(
            List<String> oTokens, String fullPageNorm) {
        if (oTokens == null || fullPageNorm == null || fullPageNorm.isEmpty()) {
            return false;
        }
        for (String tok : oTokens) {
            if (tok == null || tok.length() < 4) {
                continue;
            }
            if (!hybridDedupTokenMatchesLine(tok, fullPageNorm)) {
                return true;
            }
        }
        return false;
    }

    private static boolean hybridDedupTokenMatchesLine(String tok, String lineLower) {
        if (tok == null || tok.isEmpty() || lineLower == null) return false;
        if (lineLower.contains(tok)) return true;
        if (tok.startsWith("fsm") && lineLower.contains("fsm")) return true;
        if (tok.length() < 4 || tok.length() > 12) return false;
        for (String w : lineLower.split("[^a-z0-9]+")) {
            if (w.length() < 3) continue;
            if (Math.abs(w.length() - tok.length()) > 2) continue;
            if (hybridLevenshteinSmall(tok, w) <= 1) return true;
        }
        return false;
    }

    /** 仅用于短串（≤12）的编辑距离，避免性能问题 */
    private static int hybridLevenshteinSmall(String a, String b) {
        int n = a.length();
        int m = b.length();
        if (n > 12 || m > 12) return 99;
        if (n == 0) return m;
        if (m == 0) return n;
        int[] prev = new int[m + 1];
        int[] cur = new int[m + 1];
        for (int j = 0; j <= m; j++) {
            prev[j] = j;
        }
        for (int i = 1; i <= n; i++) {
            cur[0] = i;
            char ca = a.charAt(i - 1);
            for (int j = 1; j <= m; j++) {
                int cost = ca == b.charAt(j - 1) ? 0 : 1;
                cur[j] = Math.min(Math.min(cur[j - 1] + 1, prev[j] + 1), prev[j - 1] + cost);
            }
            int[] tmp = prev;
            prev = cur;
            cur = tmp;
        }
        return prev[m];
    }

    /**
     * 如 OCR 仅识别出「(FSM)」而文本层标题已有「Finite State Machine (FSM)」，不应再译一遍。
     */
    private static boolean hybridOcrIsRedundantParentheticalAcronym(
            CoordinateTextStripper.TextItem o, List<CoordinateTextStripper.TextItem> textLayerItems) {
        if (o == null || o.text == null || textLayerItems == null) return false;
        String compact = normalizeTextForHybridDedup(o.text).replaceAll("\\s+", "");
        if (compact.length() < 4 || compact.length() > 18) return false;
        if (!(compact.startsWith("(") && compact.endsWith(")"))) return false;
        String inner = compact.substring(1, compact.length() - 1);
        if (inner.length() < 2 || inner.length() > 12) return false;
        if (!inner.matches("[a-z0-9]+")) return false;
        final float slackY = 100f;
        String combinedNear = buildTextLayerConcatNormalizedNearY(textLayerItems, o.y, slackY);
        if (combinedNear.contains("(" + inner + ")")) return true;
        if (inner.equals("fsm") && (combinedNear.contains("finite state machine")
                || combinedNear.contains("state machine"))) {
            return true;
        }
        for (CoordinateTextStripper.TextItem t : textLayerItems) {
            if (t == null || t.text == null) continue;
            if (Math.abs(o.y - t.y) > slackY) continue;
            String tt = normalizeTextForHybridDedup(t.text);
            if (tt.contains("(" + inner + ")")) return true;
            if (inner.equals("fsm") && (tt.contains("finite state machine") || tt.contains("state machine"))) {
                return true;
            }
        }
        return false;
    }

    /**
     * 使用OCR从PDF页面提取文本（与普通文本提取方式一致）
     */
    private static List<CoordinateTextStripper.TextItem> extractTextWithOCR(
            PDDocument document, PDPage page, int pageIndex) throws Exception {

        // 初始化OCR引擎
        Tesseract tesseract;
        try {
            tesseract = initializeTesseract();
        } catch (Exception e) {
            throw new Exception("OCR引擎初始化失败: " + e.getMessage(), e);
        }

        // 将PDF页面渲染为图片
        BufferedImage image = renderPageImageForOcr(document, pageIndex);

        // 获取页面尺寸
        float pageWidth = page.getMediaBox().getWidth();
        float pageHeight = page.getMediaBox().getHeight();

        try {
            // 使用Tesseract进行OCR识别，获取带坐标的结果
            // 使用getWords方法获取每个单词的边界框信息
            System.out.println("  [OCR识别] 开始识别图片中的文本（DPI=" + OCR_DPI + "）...");
            java.util.List<net.sourceforge.tess4j.Word> words = tesseract.getWords(image, 1);

            if (words == null || words.isEmpty()) {
                System.out.println("  [OCR识别] 未识别到任何文本");
                return new ArrayList<>();
            }

            System.out.println("  [OCR识别] 成功识别到 " + words.size() + " 个单词");

            // 将OCR结果转换为TextItem列表（使用实际坐标）
            // 与普通文本提取返回的格式完全一致
            List<CoordinateTextStripper.TextItem> textItems = parseOCRWordsToTextItems(
                    words, pageWidth, pageHeight, image.getWidth(), image.getHeight());

            // 输出OCR识别的前几个文本项，帮助用户了解识别情况
            if (!textItems.isEmpty()) {
                System.out.println("  [OCR识别] 识别到的文本示例（前5个）:");
                int sampleCount = Math.min(5, textItems.size());
                for (int i = 0; i < sampleCount; i++) {
                    CoordinateTextStripper.TextItem item = textItems.get(i);
                    System.out.println("    [" + (i + 1) + "] \"" + item.text + "\" (Y=" + item.y + ")");
                }
                if (textItems.size() > 5) {
                    System.out.println("    ... 还有 " + (textItems.size() - 5) + " 个文本项");
                }
            }

            return textItems;

        } catch (Exception e) {
            // getWords可能抛出各种异常，统一捕获并转换
            throw new Exception("OCR识别失败: " + e.getMessage(), e);
        }
    }

    /**
     * 图片预处理以提高OCR识别率
     */
    private static BufferedImage preprocessImage(BufferedImage image) {
        // 转换为RGB格式
        BufferedImage processed = new BufferedImage(
                image.getWidth(), image.getHeight(), BufferedImage.TYPE_INT_RGB);
        Graphics2D g = processed.createGraphics();

        // 设置高质量渲染
        g.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_BILINEAR);
        g.setRenderingHint(RenderingHints.KEY_RENDERING, RenderingHints.VALUE_RENDER_QUALITY);
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);

        g.drawImage(image, 0, 0, null);
        g.dispose();

        // 增强对比度以提高OCR识别率
        // 对于包含表格和复杂布局的幻灯片，灰度转换和对比度增强可以显著提高识别率
        try {
            processed = ImageHelper.convertImageToGrayscale(processed);
            processed = increaseImageContrast(processed);
            System.out.println("  [OCR预处理] 已应用灰度转换和对比度增强");
        } catch (Exception e) {
            System.out.println("  [OCR预处理] 图片增强失败，使用原始图片: " + e.getMessage());
        }

        return processed;
    }

    /**
     * 增强图片对比度以提高OCR识别率
     * @param image 原始图片
     * @return 增强对比度后的图片
     */
    private static BufferedImage increaseImageContrast(BufferedImage image) {
        // 使用RescaleOp增强对比度
        // scaleFactor: 1.2 表示增加20%的对比度
        // offset: 0 表示不改变亮度
        RescaleOp rescaleOp = new RescaleOp(1.2f, 0f, null);
        BufferedImage enhanced = rescaleOp.filter(image, null);
        return enhanced;
    }

    /**
     * PascalCase 且全字母、长度≥3 时视为可能的类名/专有名词，勿当作 OCR 短噪声剔除（如 Car、Dog、Api）。
     */
    private static boolean isLikelyJavaClassLikeIdentifier(String lettersOnly) {
        if (lettersOnly == null || lettersOnly.length() < 3) {
            return false;
        }
        if (!Character.isUpperCase(lettersOnly.charAt(0))) {
            return false;
        }
        for (int i = 1; i < lettersOnly.length(); i++) {
            if (!Character.isLetter(lettersOnly.charAt(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * 修复耦合课件中常见 OCR：高亮类名读成「class」、旁注「Car Traveler tightly coupled Car」并入句尾。
     */
    private static String repairOcrCouplingSlideGarble(String s) {
        if (s == null || s.isEmpty()) {
            return s;
        }
        String lower = s.toLowerCase();
        if (!lower.contains("traveler") || !lower.contains("reference of class")) {
            return s;
        }
        String t = s.replaceFirst("(?i)(reference\\s+of)\\s+class", "$1 Car class");
        if (lower.contains("class is with class")) {
            t = t.replaceFirst("(?i)class\\s+is\\s+with\\s+class", "Traveler class is tightly coupled with Car class");
            t = t.replaceFirst("(?i)\\s*(Car\\s+)?Traveler\\s+tightly\\s+coupled\\s+Car\\s*\\.?\\s*$", "");
        }
        return t.replaceAll("\\s+", " ").trim();
    }

    /**
     * 清理OCR文本，移除明显错误的前缀/后缀
     * @param text 原始文本
     * @return 清理后的文本
     */
    private static String cleanOCRText(String text) {
        if (text == null || text.trim().isEmpty()) {
            return text;
        }

        String cleaned = text.trim();

        // 移除明显OCR错误的前缀（如 "Bx Pps AH"）
        // 检查文本开头是否有无意义的短单词组合
        String[] words = cleaned.split("\\s+");
        if (words.length > 2) {
            // 检查前几个单词是否是OCR错误
            int validStartIndex = 0;
            for (int i = 0; i < Math.min(3, words.length); i++) {
                String word = words[i].replaceAll("[^a-zA-Z]", "");
                if (!word.isEmpty() && isLikelyJavaClassLikeIdentifier(word)) {
                    break;
                }
                // 如果是无意义的短单词（2-3个字母，无元音或很少元音），可能是OCR错误
                if (word.length() <= 3 && word.length() >= 2) {
                    int vowelCount = 0;
                    for (char c : word.toLowerCase().toCharArray()) {
                        if (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u') {
                            vowelCount++;
                        }
                    }
                    // 如果没有元音或只有1个元音，且不是常见单词，可能是OCR错误
                    if (vowelCount == 0 || (vowelCount == 1 && word.length() == 3)) {
                        // 检查是否是常见单词
                        String[] commonWords = {"the", "and", "for", "are", "but", "not", "you", "all", "can", "her", "was", "one", "our", "out", "day", "get", "has", "him", "his", "how", "man", "new", "now", "old", "see", "two", "way", "who", "boy", "did", "its", "let", "put", "say", "she", "too", "use"};
                        boolean isCommonWord = false;
                        for (String common : commonWords) {
                            if (word.equalsIgnoreCase(common)) {
                                isCommonWord = true;
                                break;
                            }
                        }
                        if (!isCommonWord) {
                            validStartIndex = i + 1;
                            continue;
                        }
                    }
                }
                // 如果找到有效的单词，停止检查
                break;
            }

            // 如果找到了有效起始位置，移除前面的OCR错误
            if (validStartIndex > 0) {
                StringBuilder sb = new StringBuilder();
                for (int i = validStartIndex; i < words.length; i++) {
                    if (i > validStartIndex) sb.append(" ");
                    sb.append(words[i]);
                }
                cleaned = sb.toString().trim();
                System.out.println("  [文本清理] 移除OCR错误前缀: \"" + text + "\" -> \"" + cleaned + "\"");
            }
        }

        // 移除明显OCR错误的后缀（类似逻辑）
        words = cleaned.split("\\s+");
        if (words.length > 2) {
            int validEndIndex = words.length;
            for (int i = words.length - 1; i >= Math.max(0, words.length - 3); i--) {
                String word = words[i].replaceAll("[^a-zA-Z]", "");
                if (!word.isEmpty() && isLikelyJavaClassLikeIdentifier(word)) {
                    break;
                }
                if (word.length() <= 3 && word.length() >= 2) {
                    int vowelCount = 0;
                    for (char c : word.toLowerCase().toCharArray()) {
                        if (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u') {
                            vowelCount++;
                        }
                    }
                    if (vowelCount == 0 || (vowelCount == 1 && word.length() == 3)) {
                        String[] commonWords = {"the", "and", "for", "are", "but", "not", "you", "all", "can", "her", "was", "one", "our", "out", "day", "get", "has", "him", "his", "how", "man", "new", "now", "old", "see", "two", "way", "who", "boy", "did", "its", "let", "put", "say", "she", "too", "use"};
                        boolean isCommonWord = false;
                        for (String common : commonWords) {
                            if (word.equalsIgnoreCase(common)) {
                                isCommonWord = true;
                                break;
                            }
                        }
                        if (!isCommonWord) {
                            validEndIndex = i;
                            continue;
                        }
                    }
                }
                break;
            }

            if (validEndIndex < words.length) {
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < validEndIndex; i++) {
                    if (i > 0) sb.append(" ");
                    sb.append(words[i]);
                }
                cleaned = sb.toString().trim();
                System.out.println("  [文本清理] 移除OCR错误后缀: \"" + text + "\" -> \"" + cleaned + "\"");
            }
        }

        String repaired = repairOcrCouplingSlideGarble(cleaned);
        if (!repaired.equals(cleaned)) {
            System.out.println("  [文本清理] OCR句式修复: \"" + cleaned + "\" -> \"" + repaired + "\"");
            cleaned = repaired;
        }

        return cleaned;
    }

    /**
     * 检测OCR识别的文本质量，过滤掉明显错误的识别结果
     * @param text OCR识别的文本
     * @return true表示文本质量可接受，false表示可能是错误的识别结果
     */
    /**
     * 将OCR识别的单词列表解析为TextItem列表（使用实际坐标）
     * 从Tesseract的Word对象中获取边界框信息，转换为PDF坐标
     */
    private static List<CoordinateTextStripper.TextItem> parseOCRWordsToTextItems(
            java.util.List<net.sourceforge.tess4j.Word> words, float pageWidth, float pageHeight,
            int imageWidth, int imageHeight) {

        List<CoordinateTextStripper.TextItem> textItems = new ArrayList<>();

        if (words == null || words.isEmpty()) {
            return textItems;
        }

        // 处理每个单词
        for (net.sourceforge.tess4j.Word word : words) {
            String text = word.getText();
            if (text == null || text.trim().isEmpty()) {
                continue;
            }

            java.awt.Rectangle bbox = word.getBoundingBox();
            if (bbox == null) {
                continue;
            }

            CoordinateTextStripper.TextItem ti = ocrImageBBoxToTextItem(
                    text.trim(), bbox, pageWidth, pageHeight, imageWidth, imageHeight);
            if (ti != null) {
                textItems.add(ti);
            }
        }

        return textItems;
    }

    /**
     * 将图片像素框转为与文本层一致的 TextItem（y 为自上而下、数值越大越靠下）
     */
    private static CoordinateTextStripper.TextItem ocrImageBBoxToTextItem(
            String text, Rectangle bbox, float pageWidth, float pageHeight,
            int imageWidth, int imageHeight) {
        if (text == null || text.trim().isEmpty() || bbox == null) {
            return null;
        }
        float scaleX = pageWidth / imageWidth;
        float scaleY = pageHeight / imageHeight;
        float x = bbox.x * scaleX;
        float imageYFromTop = bbox.y;
        float imageYFromBottom = imageHeight - imageYFromTop - bbox.height;
        float pdfYFromBottom = imageYFromBottom * scaleY;
        float pdfYTop = pdfYFromBottom + (bbox.height * scaleY);
        float yTopDown = pageHeight - pdfYTop;
        return new CoordinateTextStripper.TextItem(text.trim(), x, yTopDown);
    }

    /** 混合 OCR：同一水平带内若相邻词水平间距过大，拆成独立片段（避免左栏句子与右侧示意图标签连成一行） */
    private static final class HybridOcrWordBox {
        final Rectangle r;
        final String text;

        HybridOcrWordBox(Rectangle r, String text) {
            this.r = r;
            this.text = text;
        }

        int centerY() {
            return r.y + r.height / 2;
        }

        int right() {
            return r.x + r.width;
        }
    }

    private static List<CoordinateTextStripper.TextItem> hybridSplitOcrWordsToTextItems(
            List<net.sourceforge.tess4j.Word> kept, float pageWidth, float pageHeight, int imgW, int imgH) {
        List<HybridOcrWordBox> boxes = new ArrayList<>();
        for (net.sourceforge.tess4j.Word w : kept) {
            if (w == null || w.getText() == null) {
                continue;
            }
            String t = w.getText().trim();
            if (t.isEmpty()) {
                continue;
            }
            Rectangle r = w.getBoundingBox();
            if (r == null || r.width <= 0 || r.height <= 0) {
                continue;
            }
            boxes.add(new HybridOcrWordBox(r, t));
        }
        if (boxes.isEmpty()) {
            return new ArrayList<>();
        }

        float yTol = Math.max(14f, imgH / 100f);
        float xGapFloor = Math.max(56f, imgW * 0.026f);

        boxes.sort(Comparator.comparingInt(HybridOcrWordBox::centerY).thenComparingInt(b -> b.r.x));

        TreeMap<Integer, List<HybridOcrWordBox>> lineBuckets = new TreeMap<>();
        for (HybridOcrWordBox b : boxes) {
            int key = (int) Math.round(b.centerY() / yTol);
            lineBuckets.computeIfAbsent(key, k -> new ArrayList<>()).add(b);
        }

        List<CoordinateTextStripper.TextItem> out = new ArrayList<>();
        for (List<HybridOcrWordBox> band : lineBuckets.values()) {
            band.sort(Comparator.comparingInt(b -> b.r.x));
            List<Integer> widths = new ArrayList<>(band.size());
            for (HybridOcrWordBox w : band) {
                widths.add(Math.max(1, w.r.width));
            }
            Collections.sort(widths);
            int medW = widths.get(widths.size() / 2);
            float splitGap = Math.max(xGapFloor, medW * 3.8f);

            List<HybridOcrWordBox> seg = new ArrayList<>();
            for (HybridOcrWordBox wb : band) {
                if (!seg.isEmpty()) {
                    int gap = wb.r.x - seg.get(seg.size() - 1).right();
                    if (gap > splitGap) {
                        flushHybridOcrWordSegment(seg, out, pageWidth, pageHeight, imgW, imgH);
                        seg = new ArrayList<>();
                    }
                }
                seg.add(wb);
            }
            if (!seg.isEmpty()) {
                flushHybridOcrWordSegment(seg, out, pageWidth, pageHeight, imgW, imgH);
            }
        }
        return out;
    }

    private static void flushHybridOcrWordSegment(
            List<HybridOcrWordBox> seg, List<CoordinateTextStripper.TextItem> out,
            float pageWidth, float pageHeight, int imgW, int imgH) {
        if (seg == null || seg.isEmpty()) {
            return;
        }
        int minX = Integer.MAX_VALUE;
        int minY = Integer.MAX_VALUE;
        int maxR = Integer.MIN_VALUE;
        int maxB = Integer.MIN_VALUE;
        StringBuilder sb = new StringBuilder();
        for (HybridOcrWordBox w : seg) {
            if (sb.length() > 0) {
                sb.append(' ');
            }
            sb.append(w.text);
            minX = Math.min(minX, w.r.x);
            minY = Math.min(minY, w.r.y);
            maxR = Math.max(maxR, w.r.x + w.r.width);
            maxB = Math.max(maxB, w.r.y + w.r.height);
        }
        Rectangle union = new Rectangle(minX, minY, maxR - minX, maxB - minY);
        CoordinateTextStripper.TextItem ti = ocrImageBBoxToTextItem(sb.toString(), union,
                pageWidth, pageHeight, imgW, imgH);
        if (ti != null) {
            out.add(ti);
        }
    }

    /**
     * 遍历页面内容流，记录像素面积足够大的 {@code drawImage} 在用户空间中的轴对齐包围盒（用于判断是否为页脚校徽等）。
     */
    private static final class HybridEmbeddedImageBoundsCollector extends PDFGraphicsStreamEngine {

        private final List<Rectangle2D.Float> largeImageBounds = new ArrayList<>();

        private HybridEmbeddedImageBoundsCollector(PDPage page) throws IOException {
            super(page);
        }

        @Override
        public void drawImage(PDImage pdImage) throws IOException {
            long px = (long) pdImage.getWidth() * (long) pdImage.getHeight();
            if (px < MIN_RASTER_IMAGE_PIXELS) {
                return;
            }
            Matrix ctm = getGraphicsState().getCurrentTransformationMatrix();
            float iw = pdImage.getWidth();
            float ih = pdImage.getHeight();
            Point2D.Float p00 = ctm.transformPoint(0, 0);
            Point2D.Float piw0 = ctm.transformPoint(iw, 0);
            Point2D.Float p0ih = ctm.transformPoint(0, ih);
            Point2D.Float piwih = ctm.transformPoint(iw, ih);
            float minX = min4(p00.x, piw0.x, p0ih.x, piwih.x);
            float maxX = max4(p00.x, piw0.x, p0ih.x, piwih.x);
            float minY = min4(p00.y, piw0.y, p0ih.y, piwih.y);
            float maxY = max4(p00.y, piw0.y, p0ih.y, piwih.y);
            largeImageBounds.add(new Rectangle2D.Float(minX, minY, maxX - minX, maxY - minY));
        }

        @Override
        public void appendRectangle(Point2D p0, Point2D p1, Point2D p2, Point2D p3) throws IOException {
        }

        @Override
        public void clip(int windingRule) throws IOException {
        }

        @Override
        public void moveTo(float x, float y) throws IOException {
        }

        @Override
        public void lineTo(float x, float y) throws IOException {
        }

        @Override
        public void curveTo(float x1, float y1, float x2, float y2, float x3, float y3) throws IOException {
        }

        @Override
        public Point2D getCurrentPoint() throws IOException {
            return new Point2D.Float(0, 0);
        }

        @Override
        public void closePath() throws IOException {
        }

        @Override
        public void endPath() throws IOException {
        }

        @Override
        public void strokePath() throws IOException {
        }

        @Override
        public void fillPath(int windingRule) throws IOException {
        }

        @Override
        public void fillAndStrokePath(int windingRule) throws IOException {
        }

        @Override
        public void shadingFill(COSName shadingName) throws IOException {
        }

        private static float min4(float a, float b, float c, float d) {
            return Math.min(Math.min(a, b), Math.min(c, d));
        }

        private static float max4(float a, float b, float c, float d) {
            return Math.max(Math.max(a, b), Math.max(c, d));
        }
    }
}
